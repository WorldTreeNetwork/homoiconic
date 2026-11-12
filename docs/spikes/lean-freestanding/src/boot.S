/* Entry from Cloud Hypervisor's direct kernel boot (PVH): 32-bit protected
   mode, paging off, %ebx = hvm_start_info. Reach 64-bit mode with the first
   4 GiB mapped one-to-one, then call kmain. */

	.section .note.Xen, "a", @note
	.balign 4
	.long 4            /* name size */
	.long 4            /* descriptor size */
	.long 18           /* XEN_ELFNOTE_PHYS32_ENTRY */
	.asciz "Xen"
	.long pvh_start32

	.section .bss.boot, "aw", @nobits
	.balign 4096
pml4:	.skip 4096
pdpt:	.skip 4096
pd:	.skip 4096 * 4
	.skip 65536
boot_stack_top:

	.section .rodata.boot, "a"
	.balign 16
gdt:
	.quad 0
	.quad 0x00af9a000000ffff   /* 0x08: 64-bit code */
	.quad 0x00cf92000000ffff   /* 0x10: data */
gdt_end:
gdt_ptr:
	.word gdt_end - gdt - 1
	.long gdt
	.long 0

	.section .text.boot, "ax"
	.code32
	.globl pvh_start32
pvh_start32:
	cli
	movl $boot_stack_top, %esp
	movl %ebx, %esi                /* keep start_info */

	/* 2 MiB pages for 0..4 GiB */
	movl $pd, %edi
	xorl %ecx, %ecx
1:	movl %ecx, %eax
	shll $21, %eax
	orl  $0x83, %eax               /* present, writable, large */
	movl %eax, (%edi,%ecx,8)
	movl %ecx, %eax
	shrl $11, %eax
	movl %eax, 4(%edi,%ecx,8)
	incl %ecx
	cmpl $2048, %ecx
	jne 1b

	movl $pdpt, %edi
	movl $pd, %eax
	xorl %ecx, %ecx
2:	movl %eax, %edx
	orl  $0x3, %edx
	movl %edx, (%edi,%ecx,8)
	movl $0, 4(%edi,%ecx,8)
	addl $4096, %eax
	incl %ecx
	cmpl $4, %ecx
	jne 2b

	movl $pdpt, %eax
	orl  $0x3, %eax
	movl %eax, pml4
	movl $0, pml4 + 4

	movl %cr4, %eax
	orl  $0x620, %eax              /* PAE, OSFXSR, OSXMMEXCPT */
	movl %eax, %cr4
	movl $pml4, %eax
	movl %eax, %cr3
	movl $0xc0000080, %ecx         /* EFER */
	rdmsr
	orl  $0x101, %eax              /* long mode, syscall */
	wrmsr
	movl %cr0, %eax
	andl $0xfffffffb, %eax         /* clear EM */
	orl  $0x80000023, %eax         /* paging, PE, MP, NE */
	movl %eax, %cr0
	lgdt gdt_ptr
	ljmp $0x08, $start64

	.code64
start64:
	movw $0x10, %ax
	movw %ax, %ds
	movw %ax, %es
	movw %ax, %ss
	xorl %eax, %eax
	movw %ax, %fs
	movw %ax, %gs
	fninit

	/* Extended state: turn on XSAVE and AVX where the processor has them. */
	movl $1, %eax
	cpuid
	btl  $26, %ecx                 /* XSAVE */
	jnc  3f
	movq %cr4, %rax
	orq  $0x40000, %rax            /* OSXSAVE */
	movq %rax, %cr4
	movl $1, %eax
	cpuid
	movl $3, %eax
	btl  $28, %ecx                 /* AVX */
	jnc  4f
	movl $7, %eax
4:	xorl %edx, %edx
	xorl %ecx, %ecx
	xsetbv
3:
	movl %esi, %edi                /* start_info */
	xorl %ebp, %ebp
	call kmain
5:	hlt
	jmp 5b

/* enter_program(entry, stack): start the C library with the stack kmain built. */
	.globl enter_program
enter_program:
	movq %rsi, %rsp
	xorl %edx, %edx
	xorl %ebp, %ebp
	jmp *%rdi

/* The C library reaches the system with the syscall instruction. There is no
   other privilege level here, so it arrives on the caller's stack. Everything
   but %rax, %rcx and %r11 is preserved, including the vector registers. */
	.globl syscall_entry
syscall_entry:
	leaq -128(%rsp), %rsp          /* the caller's red zone */
	pushq %rcx
	pushq %r11
	pushq %rbp
	pushq %r12
	pushq %r9
	pushq %r8
	pushq %r10
	pushq %rdx
	pushq %rsi
	pushq %rdi
	pushq %rax
	movq %rsp, %rdi                /* frame: nr, a1..a6 */
	movq %rsp, %rbp
	subq $4096, %rsp
	andq $-64, %rsp
	xorl %eax, %eax
	movq %rax, 512(%rsp)
	movq %rax, 520(%rsp)
	movq %rax, 528(%rsp)
	movq %rax, 536(%rsp)
	movq %rax, 544(%rsp)
	movq %rax, 552(%rsp)
	movq %rax, 560(%rsp)
	movq %rax, 568(%rsp)
	movl $-1, %eax
	movl $-1, %edx
	xsave64 (%rsp)
	movq %rsp, %r12
	call syscall_dispatch
	movq %rax, %rcx
	movl $-1, %eax
	movl $-1, %edx
	xrstor64 (%r12)
	movq %rcx, %rax
	movq %rbp, %rsp
	addq $8, %rsp
	popq %rdi
	popq %rsi
	popq %rdx
	popq %r10
	popq %r8
	popq %r9
	popq %r12
	popq %rbp
	popq %r11
	popq %rcx
	pushq %r11
	popfq
	leaq 128(%rsp), %rsp
	jmp *%rcx

/* Faults: say what happened and stop. */
	.section .text.boot
	.macro fault_noerr n
	.balign 16
	pushq $0
	pushq $\n
	jmp fault_common
	.endm
	.macro fault_err n
	.balign 16
	pushq $\n
	jmp fault_common
	.endm
	.globl fault_stubs
	.balign 16
fault_stubs:
	.irp n, 0,1,2,3,4,5,6,7
	fault_noerr \n
	.endr
	fault_err 8
	fault_noerr 9
	.irp n, 10,11,12,13,14
	fault_err \n
	.endr
	.irp n, 15,16
	fault_noerr \n
	.endr
	fault_err 17
	.irp n, 18,19,20
	fault_noerr \n
	.endr
	fault_err 21
	.irp n, 22,23,24,25,26,27,28,29,30,31
	fault_noerr \n
	.endr
fault_common:
	movq 0(%rsp), %rdi             /* vector */
	movq 8(%rsp), %rsi             /* error code */
	movq 16(%rsp), %rdx            /* rip */
	movq %cr2, %rcx
	movq 40(%rsp), %r8             /* rsp */
	andq $-16, %rsp
	call fault_report
6:	hlt
	jmp 6b

	.section .note.GNU-stack, "", @progbits

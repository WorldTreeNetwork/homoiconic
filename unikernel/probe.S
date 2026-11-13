/* probe_preserve(): set every piece of state a system call must give back,
   make the check's system call (its handler overwrites the vector registers
   and the floating-point control words), and compare. Returns 0, or a number
   that says which comparison failed. */

	.section .rodata
	.balign 32
pattern:
	.set i, 0
	.rept 16
	.quad 0x0101010101010101 * (i + 1), 0x1010101010101010 * (i + 1)
	.quad 0x0303030303030303 * (i + 1), 0x3030303030303030 * (i + 1)
	.set i, i + 1
	.endr
mxcsr_set:	.long 0x5f80           /* round toward zero */
fpucw_set:	.word 0x0f7f           /* round toward zero */

	.text
	.globl probe_preserve
probe_preserve:
	pushq %rbx
	pushq %rbp
	pushq %r12
	pushq %r13
	pushq %r14
	pushq %r15
	subq $1024, %rsp               /* 0..511 scratch; the red zone is below %rsp */

	/* AVX usable? XCR0 bit 2. Keep the answer in the scratch area. */
	xorl %ecx, %ecx
	xgetbv
	andl $4, %eax
	movl %eax, 512(%rsp)

	leaq pattern(%rip), %rsi
	.irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	movdqu \i * 32(%rsi), %xmm\i
	.endr
	cmpl $0, 512(%rsp)
	je 1f
	.irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	vmovdqu \i * 32(%rsi), %ymm\i
	.endr
1:
	ldmxcsr mxcsr_set(%rip)
	fldcw fpucw_set(%rip)
	fld1                          /* x87 data as well as its control word */

	/* the red zone: 16 words under the stack pointer */
	movq $0x7ed0000000000000, %rax
	.set i, 1
	.rept 16
	movq %rax, -8 * i(%rsp)
	incq %rax
	.set i, i + 1
	.endr

	movq $0xb0b0b0b0b0b0b0b0, %rbx
	movq $0xb1b1b1b1b1b1b1b1, %rbp
	movq $0xc2c2c2c2c2c2c2c2, %r12
	movq $0xc3c3c3c3c3c3c3c3, %r13
	movq $0xc4c4c4c4c4c4c4c4, %r14
	movq $0xc5c5c5c5c5c5c5c5, %r15
	movq $0xd0d0d0d0d0d0d0d0, %rsi
	movq $0xd1d1d1d1d1d1d1d1, %rdx
	movq $0xd2d2d2d2d2d2d2d2, %r10
	movq $0xd3d3d3d3d3d3d3d3, %r8
	movq $0xd4d4d4d4d4d4d4d4, %r9
	movl $1, %edi
	movl $1000, %eax
	stc
	syscall
	jnc fail1                      /* 1: the carry flag */
	cmpq $77, %rax
	jne fail2                      /* 2: the result */
	cmpq $1, %rdi
	jne fail3                      /* 3: an argument register */
	movq $0xd0d0d0d0d0d0d0d0, %rax
	cmpq %rax, %rsi
	jne fail3
	movq $0xd1d1d1d1d1d1d1d1, %rax
	cmpq %rax, %rdx
	jne fail3
	movq $0xd2d2d2d2d2d2d2d2, %rax
	cmpq %rax, %r10
	jne fail3
	movq $0xd3d3d3d3d3d3d3d3, %rax
	cmpq %rax, %r8
	jne fail3
	movq $0xd4d4d4d4d4d4d4d4, %rax
	cmpq %rax, %r9
	jne fail3
	movq $0xb0b0b0b0b0b0b0b0, %rax
	cmpq %rax, %rbx
	jne fail4                      /* 4: a register the callee keeps */
	movq $0xb1b1b1b1b1b1b1b1, %rax
	cmpq %rax, %rbp
	jne fail4
	movq $0xc2c2c2c2c2c2c2c2, %rax
	cmpq %rax, %r12
	jne fail4
	movq $0xc3c3c3c3c3c3c3c3, %rax
	cmpq %rax, %r13
	jne fail4
	movq $0xc4c4c4c4c4c4c4c4, %rax
	cmpq %rax, %r14
	jne fail4
	movq $0xc5c5c5c5c5c5c5c5, %rax
	cmpq %rax, %r15
	jne fail4

	movq $0x7ed0000000000000, %rax
	.set i, 1
	.rept 16
	cmpq %rax, -8 * i(%rsp)
	jne fail5                      /* 5: the red zone */
	incq %rax
	.set i, i + 1
	.endr

	/* control words */
	stmxcsr 516(%rsp)
	movl 516(%rsp), %eax
	andl $0xffc0, %eax             /* not the sticky status bits */
	cmpl $0x5f80, %eax
	jne fail6                      /* 6: the vector control word */
	fnstcw 520(%rsp)
	cmpw $0x0f7f, 520(%rsp)
	jne fail7                      /* 7: the floating-point control word */

	fstpl 528(%rsp)
	movq $0x3ff0000000000000, %rax /* the double 1.0 */
	cmpq %rax, 528(%rsp)
	jne fail7

	/* vector registers: store each and compare with its pattern */
	cmpl $0, 512(%rsp)
	je 2f
	.irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	vmovdqu %ymm\i, \i * 32(%rsp)
	.endr
	vzeroupper
	movl $512, %ecx
	jmp 3f
2:	.irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
	movdqu %xmm\i, \i * 32(%rsp)
	.endr
	/* compare 16 bytes of each 32 */
	leaq pattern(%rip), %rsi
	movq %rsp, %rdi
	movl $16, %edx
4:	movq (%rsi), %rax
	cmpq %rax, (%rdi)
	jne fail8
	movq 8(%rsi), %rax
	cmpq %rax, 8(%rdi)
	jne fail8
	addq $32, %rsi
	addq $32, %rdi
	decl %edx
	jnz 4b
	jmp ok
3:	leaq pattern(%rip), %rsi
	movq %rsp, %rdi
	cld
	repe cmpsb
	jne fail8                      /* 8: a vector register */
ok:	xorl %eax, %eax
	jmp done
fail1:	movl $1, %eax
	jmp done
fail2:	movl $2, %eax
	jmp done
fail3:	movl $3, %eax
	jmp done
fail4:	movl $4, %eax
	jmp done
fail5:	movl $5, %eax
	jmp done
fail6:	movl $6, %eax
	jmp done
fail7:	movl $7, %eax
	jmp done
fail8:	movl $8, %eax
done:
	/* back to the usual control words before returning to compiled code */
	movl $0x1f80, 516(%rsp)
	ldmxcsr 516(%rsp)
	fninit
	addq $1024, %rsp
	popq %r15
	popq %r14
	popq %r13
	popq %r12
	popq %rbp
	popq %rbx
	ret

	.section .note.GNU-stack, "", @progbits

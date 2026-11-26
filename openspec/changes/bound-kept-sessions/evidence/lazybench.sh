#!/bin/sh
# Lazy CostBench cases at two budgets; run from kernel/.
export PATH="$HOME/.elan/bin:$PATH"
lake build reflectCostBench > /dev/null 2>&1 || { echo "build failed"; exit 1; }
B=.lake/build/bin/reflectCostBench
for budget in 100000 100000000; do
while read -r name size; do
  timeout 300 $B lazy $name $size $budget || echo "lazy $name size=$size budget=$budget TIMEOUT-or-fail"
done <<CASES
loop 0
equal-doubled 20
equal-doubled 40
equal-light 30
equal-text 1000000
equal-big 1000000
cons-text 1000000
succ-big 1000000
case-big 1000000
access-deep 100000
add-big 1000000
sub-big 1000000
less-big 1000000
mul-big 10000
div-big 1000000
mod-big 1000000
codes-text 1000000
text-arr 1000000
add-doubled 14
add-doubled 18
add-doubled 40
literal-wide 1000
literal-wide 100000
CASES
done

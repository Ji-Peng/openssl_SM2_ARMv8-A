#! /usr/bin/env perl

# perl crypto/ec/asm/ecp_sm2-armv8.pl "linux64", $output=undef, $flavour=linux64

# $output is the last argument if it looks like a file (it has an extension)
# $flavour is the first argument if it doesn't look like a file
$output = $#ARGV >= 0 && $ARGV[$#ARGV] =~ m|\.\w+$| ? pop : undef;
$flavour = $#ARGV >= 0 && $ARGV[0] !~ m|\.| ? shift : undef;

# $0=crypto/ec/asm/ecp_sm2-armv8.pl, $1=crypto/ec/asm/
$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
# $xlate=crypto/perlasm/arm-xlate.pl used to format assembly code
( $xlate="${dir}arm-xlate.pl" and -f $xlate ) or
( $xlate="${dir}../../perlasm/arm-xlate.pl" and -f $xlate) or
die "can't locate arm-xlate.pl";
# open a pipeline and redirect standard output to this pipeline
open OUT,"| \"$^X\" $xlate $flavour \"$output\""
    or die "can't call $xlate: $!";
*STDOUT=*OUT;

{
my ($rp,$ap,$bp,$bi,$a0,$a1,$a2,$a3,$t0,$t1,$t2,$t3,$poly1,$poly3,
    $acc0,$acc1,$acc2,$acc3,$acc4,$acc5) =
    map("x$_",(0..17,19,20));

my ($acc6,$acc7)=($ap,$bp);	# used in __ecp_sm2z256_sqr_mont

$code.=<<___;
#include "arm_arch.h"

.text
___
########################################################################
# Convert ecp_sm2z256_table.c to layout expected by ecp_nistz_gather_w7
#
$0 =~ m/(.*[\/\\])[^\/\\]+$/; $dir=$1;
open TABLE,"<ecp_sm2z256_table.c"		or
open TABLE,"<${dir}../ecp_sm2z256_table.c"	or
die "failed to open ecp_sm2z256_table.c:",$!;

use integer;

foreach(<TABLE>) {
	s/TOBN\(\s*(0x[0-9a-f]+),\s*(0x[0-9a-f]+)\s*\)/push @arr,hex($2),hex($1)/geo;
}
close TABLE;

# See ecp_sm2z256_table.c for explanation for why it's 64*16*37.
# 64*16*37-1 is because $#arr returns last valid index or @arr, not
# amount of elements.
die "insane number of elements" if ($#arr != 64*16*37-1);

$code.=<<___;
.globl	ecp_sm2z256_precomputed
.type	ecp_sm2z256_precomputed,%object
.align	12
ecp_sm2z256_precomputed:
___

$gather_scatter_use_neon = 0;

########################################################################
# this conversion smashes P256_POINT_AFFINE by individual bytes with
# 64 byte interval, similar to
#	1111222233334444
#	1234123412341234
if($gather_scatter_use_neon == 0) {
	# there are 37 sub-tables, where each sub-table has 64 points
	# and each point is 64B (32B for X, 32B for Y)
	# each item of @arr is 4B, so a sub-table includes 64*64/4=64*16 items
	for(1..37) {
		@tbl = splice(@arr,0,64*16);
		for($i=0;$i<64;$i++) {
			undef @line;
			for($j=0;$j<64;$j++) {
				push @line,(@tbl[$j*16+$i/4]>>(($i%4)*8))&0xff;
			}
			$code.=".byte\t";
			$code.=join(',',map { sprintf "0x%02x",$_} @line);
			$code.="\n";
		}
	}
} else {
	# each item of @arr is 4B, 16*4B=64B = 1 point
	while (@line=splice(@arr,0,16)) {
		$code.=".word\t";
		$code.=join(',',map { sprintf "0x%08x",$_} @line);
		$code.="\n"
		# print ".word\t",join(',',map { sprintf "0x%08x",$_} @line),"\n";
	}
}

$code.=<<___;
.size	ecp_sm2z256_precomputed,.-ecp_sm2z256_precomputed

.align	5
.Lpoly: // modulus for SM2
.quad	0xffffffffffffffff,0xffffffff00000000,0xffffffffffffffff,0xfffffffeffffffff

.LRR:	// 2^512 mod P precomputed for SM2 polynomial
.quad	0x0000000200000003,0x00000002ffffffff,0x0000000100000001,0x0000000400000002

.Lone_mont: // 2^256 mod P precomputed for SM2 polynomial
.quad	0x0000000000000001,0x00000000ffffffff,0x0000000000000000,0x0000000100000000

.Lone:
.quad	1,0,0,0

.Lord:  // order n of sm2
.quad	0x53bbf40939d54123,0x7203df6b21c6052b,0xffffffffffffffff,0xfffffffeffffffff

.LordK: // LordK = low 64bits of order_inv, where order_inv * order = -1 mod 2^256
.quad	0x327f9e8872350975

.asciz	"ECP_SM2Z256 for ARMv8"

// void	ecp_sm2z256_to_mont(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_to_mont
.type	ecp_sm2z256_to_mont,%function
.align	6
ecp_sm2z256_to_mont:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]

	// pre-load b[0] to $bi, a[0-3] to $a0,$a1,$a2,$a3
	// pre-load p[1]-p[3] to $poly1-$poly3, p[0]=p[2]=0xff...ff for sm2
	ldr	$bi,.LRR		// bp[0]
	ldp	$a0,$a1,[$ap]
	ldp	$a2,$a3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24
	adr	$bp,.LRR		// &bp[0]

	// x1[4] * (R^2 mod p) where R=2^256
	bl	__ecp_sm2z256_mul_mont

	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_to_mont,.-ecp_sm2z256_to_mont

// void	ecp_sm2z256_from_mont(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_from_mont
.type	ecp_sm2z256_from_mont,%function
.align	4
ecp_sm2z256_from_mont:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]

	mov	$bi,#1			// bp[0]
	ldp	$a0,$a1,[$ap]
	ldp	$a2,$a3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24
	adr	$bp,.Lone		// &bp[0]

	// x1[4] * 1
	bl	__ecp_sm2z256_mul_mont

	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_from_mont,.-ecp_sm2z256_from_mont

// void	ecp_sm2z256_mul_mont(BN_ULONG x0[4],const BN_ULONG x1[4],
//					     const BN_ULONG x2[4]);
.globl	ecp_sm2z256_mul_mont
.type	ecp_sm2z256_mul_mont,%function
.align	4
ecp_sm2z256_mul_mont:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]

	ldr	$bi,[$bp]		// bp[0]
	ldp	$a0,$a1,[$ap]
	ldp	$a2,$a3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	bl	__ecp_sm2z256_mul_mont

	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_mul_mont,.-ecp_sm2z256_mul_mont

// void	ecp_sm2z256_sqr_mont(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_sqr_mont
.type	ecp_sm2z256_sqr_mont,%function
.align	4
ecp_sm2z256_sqr_mont:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]

	ldp	$a0,$a1,[$ap]
	ldp	$a2,$a3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	bl	__ecp_sm2z256_sqr_mont

	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_sqr_mont,.-ecp_sm2z256_sqr_mont

// void	ecp_sm2z256_add(BN_ULONG x0[4],const BN_ULONG x1[4],
//					const BN_ULONG x2[4]);
.globl	ecp_sm2z256_add
.type	ecp_sm2z256_add,%function
.align	4
ecp_sm2z256_add:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	ldp	$acc0,$acc1,[$ap]
	ldp	$t0,$t1,[$bp]
	ldp	$acc2,$acc3,[$ap,#16]
	ldp	$t2,$t3,[$bp,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	bl	__ecp_sm2z256_add

	ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_add,.-ecp_sm2z256_add

// void	ecp_sm2z256_div_by_2(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_div_by_2
.type	ecp_sm2z256_div_by_2,%function
.align	4
ecp_sm2z256_div_by_2:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	ldp	$acc0,$acc1,[$ap]
	ldp	$acc2,$acc3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	bl	__ecp_sm2z256_div_by_2

	ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		//  autiasp
	ret
.size	ecp_sm2z256_div_by_2,.-ecp_sm2z256_div_by_2

// void	ecp_sm2z256_mul_by_2(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_mul_by_2
.type	ecp_sm2z256_mul_by_2,%function
.align	4
ecp_sm2z256_mul_by_2:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	ldp	$acc0,$acc1,[$ap]
	ldp	$acc2,$acc3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24
	mov	$t0,$acc0
	mov	$t1,$acc1
	mov	$t2,$acc2
	mov	$t3,$acc3

	bl	__ecp_sm2z256_add	// ret = a+a	// 2*a

	ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_mul_by_2,.-ecp_sm2z256_mul_by_2

// void	ecp_sm2z256_mul_by_3(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_mul_by_3
.type	ecp_sm2z256_mul_by_3,%function
.align	4
ecp_sm2z256_mul_by_3:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	ldp	$acc0,$acc1,[$ap]
	ldp	$acc2,$acc3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24
	mov	$t0,$acc0
	mov	$t1,$acc1
	mov	$t2,$acc2
	mov	$t3,$acc3
	mov	$a0,$acc0
	mov	$a1,$acc1
	mov	$a2,$acc2
	mov	$a3,$acc3

	bl	__ecp_sm2z256_add	// ret = a+a	// 2*a

	mov	$t0,$a0
	mov	$t1,$a1
	mov	$t2,$a2
	mov	$t3,$a3

	bl	__ecp_sm2z256_add	// ret += a	// 2*a+a=3*a

	ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_mul_by_3,.-ecp_sm2z256_mul_by_3

// void	ecp_sm2z256_sub(BN_ULONG x0[4],const BN_ULONG x1[4],
//				        const BN_ULONG x2[4]);
.globl	ecp_sm2z256_sub
.type	ecp_sm2z256_sub,%function
.align	4
ecp_sm2z256_sub:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	ldp	$acc0,$acc1,[$ap]
	ldp	$acc2,$acc3,[$ap,#16]
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	bl	__ecp_sm2z256_sub_from

	ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_sub,.-ecp_sm2z256_sub

// void	ecp_sm2z256_neg(BN_ULONG x0[4],const BN_ULONG x1[4]);
.globl	ecp_sm2z256_neg
.type	ecp_sm2z256_neg,%function
.align	4
ecp_sm2z256_neg:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	mov	$bp,$ap
	mov	$acc0,xzr		// a = 0
	mov	$acc1,xzr
	mov	$acc2,xzr
	mov	$acc3,xzr
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	bl	__ecp_sm2z256_sub_from

	ldp	x29,x30,[sp],#16
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_neg,.-ecp_sm2z256_neg

// note that __ecp_sm2z256_mul_mont expects a[0-3] input pre-loaded
// to $a0-$a3 and b[0] - to $bi
.type	__ecp_sm2z256_mul_mont,%function
.align	4
__ecp_sm2z256_mul_mont:
	mul		$acc0,$a0,$bi		// $t0||$acc0 = a[0]*b[0]
	umulh	$t0,$a0,$bi

	mul		$acc1,$a1,$bi		// $t1||$acc1 = a[1]*b[0]
	umulh	$t1,$a1,$bi

	mul		$acc2,$a2,$bi		// $t2||$acc2 = a[2]*b[0]
	umulh	$t2,$a2,$bi

	mul		$acc3,$a3,$bi		// $t3||$acc3 = a[3]*b[0]
	umulh	$t3,$a3,$bi
	ldr		$bi,[$bp,#8]		// b[1]

	// {$acc5,$acc4,$acc3,$acc2,$acc1,$acc0}=a[3-0]*b0
	adds	$acc1,$acc1,$t0
	adcs	$acc2,$acc2,$t1
	adcs	$acc3,$acc3,$t2
	adc		$acc4,xzr,$t3
	mov		$acc5,xzr
	// $t1=$acc0, $t2=$acc0<<32, $t3=$acc0>>32 for below reduction
	mov		$t1, $acc0
	lsl		$t2, $acc0,#32
	lsr		$t3, $acc0,#32
___
for($i=1;$i<4;$i++) {

$code.=<<___;
	// reduction alternates multiplication & accumulation
	// {$acc4,$acc3,$acc2,$acc1,$acc0}=$acc5|$acc4+$t1-$t3|$acc3-$t2|$acc2-$t3|$acc1+$t1-$t2
	// add with carry propagation
	mul  	$t0, $a0, $bi			// lo(a[0]*b[i])
	adds 	$acc0, $acc1, $t1
	adcs 	$acc1, $acc2, xzr
	adcs 	$acc2, $acc3, xzr
	adcs 	$acc3, $acc4, $t1
	mul  	$t1, $a1, $bi			// lo(a[1]*b[i])
	adcs 	$acc4, $acc5, xzr
	// sub with borrow propagation
	subs 	$acc0, $acc0, $t2
	sbcs 	$acc1, $acc1, $t3
	sbcs 	$acc2, $acc2, $t2
	mul	 	$t2, $a2, $bi			// lo(a[2]*b[i])
	sbcs 	$acc3, $acc3, $t3
	mul	 	$t3, $a3, $bi			// lo(a[3]*b[i])
	sbcs 	$acc4, $acc4, xzr

	adds	$acc0,$acc0,$t0		// accumulate low parts of multiplication
	umulh	$t0,$a0,$bi			// hi(a[0]*b[i])
	adcs	$acc1,$acc1,$t1
	umulh	$t1,$a1,$bi			// hi(a[1]*b[i])
	adcs	$acc2,$acc2,$t2
	umulh	$t2,$a2,$bi			// hi(a[2]*b[i])
	adcs	$acc3,$acc3,$t3
	umulh	$t3,$a3,$bi			// hi(a[3]*b[i])
	adc		$acc4,$acc4,xzr
___
$code.=<<___	if ($i<3);
	ldr	$bi,[$bp,#8*($i+1)]	// b[$i+1]
___
$code.=<<___;
	// accumulate high parts of multiplication
	adds	$acc1,$acc1,$t0
	adcs	$acc2,$acc2,$t1
	adcs	$acc3,$acc3,$t2
	adcs	$acc4,$acc4,$t3
	adc		$acc5,xzr,xzr
	// for reduction
	mov		$t1, $acc0
	lsl		$t2, $acc0,#32
	lsr		$t3, $acc0,#32
___
}
$code.=<<___;
	// last reduction without multiplication & accumulation
	// {$acc4,$acc3,$acc2,$acc1,$acc0}=$acc5|$acc4+$t1-$t3|$acc3-$t2|$acc2-$t3|$acc1+$t1-$t2
	// add with carry propagation
	adds 	$acc0, $acc1, $t1
	adcs 	$acc1, $acc2, xzr
	adcs 	$acc2, $acc3, xzr
	adcs 	$acc3, $acc4, $t1
	adcs 	$acc4, $acc5, xzr
	// sub with borrow propagation
	subs 	$acc0, $acc0, $t2
	sbcs 	$acc1, $acc1, $t3
	sbcs 	$acc2, $acc2, $t2
	sbcs 	$acc3, $acc3, $t3
	sbcs 	$acc4, $acc4, xzr

	// note that poly0 = poly2 = 0xff...ff
	// t=out-p; if borrow then return out; else return t;
	// $acc0-poly0==$acc0-0xff...ff==$acc0-(-1)==$acc0+1
	// addition and subtraction have the same effect on flag bit
	adds	$t0,$acc0,#1
	// construct 0xff...ff
	mov		$t3,xzr
	sub		$t3,$t3,#1
	sbcs	$t1,$acc1,$poly1
	sbcs	$t2,$acc2,$t3
	sbcs	$t3,$acc3,$poly3
	sbcs	xzr,$acc4,xzr		// did it borrow?

	// ret = borrow ? ret : ret-modulus
	csel	$acc0,$acc0,$t0,lo
	csel	$acc1,$acc1,$t1,lo
	csel	$acc2,$acc2,$t2,lo
	stp		$acc0,$acc1,[$rp]
	csel	$acc3,$acc3,$t3,lo
	stp		$acc2,$acc3,[$rp,#16]

	ret
.size	__ecp_sm2z256_mul_mont,.-__ecp_sm2z256_mul_mont

// note that __ecp_sm2z256_sqr_mont expects a[0-3] input pre-loaded
// to $a0-$a3
.type	__ecp_sm2z256_sqr_mont,%function
.align	4
__ecp_sm2z256_sqr_mont:
	//  |  |  |  |  |  |a1*a0|  |
	//  |  |  |  |  |a2*a0|  |  |
	//  |  |a3*a2|a3*a0|  |  |  |
	//  |  |  |  |a2*a1|  |  |  |
	//  |  |  |a3*a1|  |  |  |  |
	// *|  |  |  |  |  |  |  | 2|
	// +|a3*a3|a2*a2|a1*a1|a0*a0|
	//  |--+--+--+--+--+--+--+--|
	//  |A7|A6|A5|A4|A3|A2|A1|A0|, where Ax is $accx, i.e. follow $accx
	//
	//  "can't overflow" below mark carrying into high part of
	//  multiplication result, which can't overflow, because it
	//  can never be all ones.

	mul		$acc1,$a1,$a0		// a[1]*a[0]
	umulh	$t1,$a1,$a0
	mul		$acc2,$a2,$a0		// a[2]*a[0]
	umulh	$t2,$a2,$a0
	mul		$acc3,$a3,$a0		// a[3]*a[0]
	umulh	$acc4,$a3,$a0

	adds	$acc2,$acc2,$t1	// accumulate high parts of multiplication
	 mul	$t0,$a2,$a1		// a[2]*a[1]
	 umulh	$t1,$a2,$a1
	adcs	$acc3,$acc3,$t2
	 mul	$t2,$a3,$a1		// a[3]*a[1]
	 umulh	$t3,$a3,$a1
	adc		$acc4,$acc4,xzr		// can't overflow

	mul		$acc5,$a3,$a2		// a[3]*a[2]
	umulh	$acc6,$a3,$a2

	adds	$t1,$t1,$t2		// accumulate high parts of multiplication
	 mul	$acc0,$a0,$a0	// a[0]*a[0]
	adc		$t2,$t3,xzr			// can't overflow

	adds	$acc3,$acc3,$t0	// accumulate low parts of multiplication
	 umulh	$a0,$a0,$a0
	adcs	$acc4,$acc4,$t1
	 mul	$t1,$a1,$a1		// a[1]*a[1]
	adcs	$acc5,$acc5,$t2
	 umulh	$a1,$a1,$a1
	adc		$acc6,$acc6,xzr		// can't overflow

	adds	$acc1,$acc1,$acc1	// acc[1-6]*=2
	 mul	$t2,$a2,$a2			// a[2]*a[2]
	adcs	$acc2,$acc2,$acc2
	 umulh	$a2,$a2,$a2
	adcs	$acc3,$acc3,$acc3
	 mul	$t3,$a3,$a3			// a[3]*a[3]
	adcs	$acc4,$acc4,$acc4
	 umulh	$a3,$a3,$a3
	adcs	$acc5,$acc5,$acc5
	adcs	$acc6,$acc6,$acc6
	adc		$acc7,xzr,xzr

	adds	$acc1,$acc1,$a0		// +a[i]*a[i]
	adcs	$acc2,$acc2,$t1
	adcs	$acc3,$acc3,$a1
	adcs	$acc4,$acc4,$t2
	adcs	$acc5,$acc5,$a2
	adcs	$acc6,$acc6,$t3
	adc		$acc7,$acc7,$a3
	
	// $t1=$acc0, $t2=$acc0<<32, $t3=$acc0>>32 for below reduction
	mov		$t1, $acc0
	lsl		$t2, $acc0,#32
	lsr		$t3, $acc0,#32
___
for($i=0;$i<3;$i++) {			# reductions, see commentary in
					# multiplication for details
$code.=<<___;
	// reduction
	adds 	$acc0, $acc1, $t1
	adcs 	$acc1, $acc2, xzr
	adcs 	$acc2, $acc3, xzr
	adcs 	$acc3, xzr, $t1
	subs 	$acc0, $acc0, $t2
	sbcs 	$acc1, $acc1, $t3
	sbcs 	$acc2, $acc2, $t2
	sbcs 	$acc3, $acc3, $t3
	// for next reduction
	mov		$t1, $acc0
	lsl		$t2, $acc0,#32
	lsr		$t3, $acc0,#32
___
}
$code.=<<___;
	// reduction
	adds 	$acc0, $acc1, $t1
	adcs 	$acc1, $acc2, xzr
	adcs 	$acc2, $acc3, xzr
	adcs 	$acc3, xzr, $t1
	subs 	$acc0, $acc0, $t2
	sbcs 	$acc1, $acc1, $t3
	sbcs 	$acc2, $acc2, $t2
	sbcs 	$acc3, $acc3, $t3

	adds	$acc0,$acc0,$acc4	// accumulate upper half
	adcs	$acc1,$acc1,$acc5
	adcs	$acc2,$acc2,$acc6
	adcs	$acc3,$acc3,$acc7
	adc		$acc4,xzr,xzr

	// note that poly0 = poly2 = 0xff...ff
	// t=out-p; if borrow then return out; else return t;
	// $acc0-poly0==$acc0-0xff...ff==$acc0-(-1)==$acc0+1
	// addition and subtraction have the same effect on flag bit
	adds	$t0,$acc0,#1
	// construct 0xff...ff
	mov		$t3,xzr
	sub		$t3,$t3,#1
	sbcs	$t1,$acc1,$poly1
	sbcs	$t2,$acc2,$t3
	sbcs	$t3,$acc3,$poly3
	sbcs	xzr,$acc4,xzr		// did it borrow?

	// ret = borrow ? ret : ret-modulus
	csel	$acc0,$acc0,$t0,lo
	csel	$acc1,$acc1,$t1,lo
	csel	$acc2,$acc2,$t2,lo
	stp		$acc0,$acc1,[$rp]
	csel	$acc3,$acc3,$t3,lo
	stp		$acc2,$acc3,[$rp,#16]

	ret
.size	__ecp_sm2z256_sqr_mont,.-__ecp_sm2z256_sqr_mont

// Note that __ecp_sm2z256_add expects both input vectors pre-loaded to
// $a0-$a3 and $t0-$t3. This is done because it's used in multiple
// contexts, e.g. in multiplication by 2 and 3...
.type	__ecp_sm2z256_add,%function
.align	4
__ecp_sm2z256_add:
	adds	$acc0,$acc0,$t0		// ret = a+b
	adcs	$acc1,$acc1,$t1
	adcs	$acc2,$acc2,$t2
	adcs	$acc3,$acc3,$t3
	adc		$ap,xzr,xzr		// zap $ap

	adds	$t0,$acc0,#1		// subs	$t0,$a0,#-1 // tmp = ret-modulus
	// construct 0xff...ff
	mov		$t3,xzr
	sub		$t3,$t3,#1
	sbcs	$t1,$acc1,$poly1
	sbcs	$t2,$acc2,$t3
	sbcs	$t3,$acc3,$poly3
	sbcs	xzr,$ap,xzr		// did subtraction borrow?

	csel	$acc0,$acc0,$t0,lo	// ret = borrow ? ret : ret-modulus
	csel	$acc1,$acc1,$t1,lo
	csel	$acc2,$acc2,$t2,lo
	stp		$acc0,$acc1,[$rp]
	csel	$acc3,$acc3,$t3,lo
	stp		$acc2,$acc3,[$rp,#16]

	ret
.size	__ecp_sm2z256_add,.-__ecp_sm2z256_add

.type	__ecp_sm2z256_sub_from,%function
.align	4
__ecp_sm2z256_sub_from:
	ldp		$t0,$t1,[$bp]
	ldp		$t2,$t3,[$bp,#16]
	subs	$acc0,$acc0,$t0		// ret = a-b
	sbcs	$acc1,$acc1,$t1
	sbcs	$acc2,$acc2,$t2
	sbcs	$acc3,$acc3,$t3
	sbc		$ap,xzr,xzr		// zap $ap

	subs	$t0,$acc0,#1		// adds	$t0,$a0,#-1 // tmp = ret+modulus
	// construct 0xff...ff
	mov		$t3,xzr
	sub		$t3,$t3,#1
	adcs	$t1,$acc1,$poly1
	adcs	$t2,$acc2,$t3
	adc		$t3,$acc3,$poly3
	cmp		$ap,xzr			// did subtraction borrow?

	csel	$acc0,$acc0,$t0,eq	// ret = borrow ? ret+modulus : ret
	csel	$acc1,$acc1,$t1,eq
	csel	$acc2,$acc2,$t2,eq
	stp		$acc0,$acc1,[$rp]
	csel	$acc3,$acc3,$t3,eq
	stp		$acc2,$acc3,[$rp,#16]

	ret
.size	__ecp_sm2z256_sub_from,.-__ecp_sm2z256_sub_from

.type	__ecp_sm2z256_sub_morf,%function
.align	4
__ecp_sm2z256_sub_morf:
	ldp		$t0,$t1,[$bp]
	ldp		$t2,$t3,[$bp,#16]
	subs	$acc0,$t0,$acc0		// ret = b-a
	sbcs	$acc1,$t1,$acc1
	sbcs	$acc2,$t2,$acc2
	sbcs	$acc3,$t3,$acc3
	sbc		$ap,xzr,xzr		// zap $ap

	subs	$t0,$acc0,#1		// adds	$t0,$a0,#-1 // tmp = ret+modulus
	// construct 0xff...ff
	mov		$t3,xzr
	sub		$t3,$t3,#1
	adcs	$t1,$acc1,$poly1
	adcs	$t2,$acc2,$t3
	adc		$t3,$acc3,$poly3
	cmp		$ap,xzr			// did subtraction borrow?

	csel	$acc0,$acc0,$t0,eq	// ret = borrow ? ret+modulus : ret
	csel	$acc1,$acc1,$t1,eq
	csel	$acc2,$acc2,$t2,eq
	stp		$acc0,$acc1,[$rp]
	csel	$acc3,$acc3,$t3,eq
	stp		$acc2,$acc3,[$rp,#16]

	ret
.size	__ecp_sm2z256_sub_morf,.-__ecp_sm2z256_sub_morf

.type	__ecp_sm2z256_div_by_2,%function
.align	4
__ecp_sm2z256_div_by_2:
	// tmp = a+modulus
	subs	$t0,$acc0,#1		// adds	$t0,$a0,#-1
	// construct 0xff...ff
	mov		$t3,xzr
	sub		$t3,$t3,#1
	adcs	$t1,$acc1,$poly1
	adcs	$t2,$acc2,$t3
	adcs	$t3,$acc3,$poly3
	adc		$ap,xzr,xzr		// zap $ap
	tst		$acc0,#1		// is a even?

	// ret = even ? a : a+modulus
	csel	$acc0,$acc0,$t0,eq
	csel	$acc1,$acc1,$t1,eq
	csel	$acc2,$acc2,$t2,eq
	csel	$acc3,$acc3,$t3,eq
	csel	$ap,xzr,$ap,eq

	// ret >>= 1
	lsr		$acc0,$acc0,#1
	orr		$acc0,$acc0,$acc1,lsl#63
	lsr		$acc1,$acc1,#1
	orr		$acc1,$acc1,$acc2,lsl#63
	lsr		$acc2,$acc2,#1
	orr		$acc2,$acc2,$acc3,lsl#63
	lsr		$acc3,$acc3,#1
	stp		$acc0,$acc1,[$rp]
	orr		$acc3,$acc3,$ap,lsl#63
	stp		$acc2,$acc3,[$rp,#16]

	ret
.size	__ecp_sm2z256_div_by_2,.-__ecp_sm2z256_div_by_2
___
########################################################################
# following subroutines are "literal" implementation of those found in
# ecp_sm2z256.c
#
########################################################################
# void ecp_sm2z256_point_double(P256_POINT *out,const P256_POINT *inp);
#
{
my ($S,$M,$Zsqr,$tmp0)=map(32*$_,(0..3));
# above map() describes stack layout with 4 temporary
# 256-bit vectors on top.
my ($rp_real,$ap_real) = map("x$_",(21,22));

$code.=<<___;
.globl	ecp_sm2z256_point_double
.type	ecp_sm2z256_point_double,%function
.align	5
ecp_sm2z256_point_double:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-96]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	sub	sp,sp,#32*4

.Ldouble_shortcut:
	ldp		$acc0,$acc1,[$ap,#32]
	 mov	$rp_real,$rp
	ldp		$acc2,$acc3,[$ap,#48]
	 mov	$ap_real,$ap
	 ldr	$poly1,.Lpoly+8
	mov		$t0,$acc0
	 ldr	$poly3,.Lpoly+24
	mov		$t1,$acc1
	 ldp	$a0,$a1,[$ap_real,#64]	// forward load for p256_sqr_mont
	mov		$t2,$acc2
	mov		$t3,$acc3
	 ldp	$a2,$a3,[$ap_real,#64+16]
	add		$rp,sp,#$S
	bl		__ecp_sm2z256_add	// p256_mul_by_2(S, in_y);

	add		$rp,sp,#$Zsqr
	bl		__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Zsqr, in_z);

	ldp		$t0,$t1,[$ap_real]
	ldp		$t2,$t3,[$ap_real,#16]
	mov		$a0,$acc0		// put Zsqr aside for p256_sub
	mov		$a1,$acc1
	mov		$a2,$acc2
	mov		$a3,$acc3
	add		$rp,sp,#$M
	bl		__ecp_sm2z256_add	// p256_add(M, Zsqr, in_x);

	add		$bp,$ap_real,#0
	mov		$acc0,$a0		// restore Zsqr
	mov		$acc1,$a1
	 ldp	$a0,$a1,[sp,#$S]	// forward load for p256_sqr_mont
	mov		$acc2,$a2
	mov		$acc3,$a3
	 ldp	$a2,$a3,[sp,#$S+16]
	add		$rp,sp,#$Zsqr
	bl		__ecp_sm2z256_sub_morf	// p256_sub(Zsqr, in_x, Zsqr);

	add		$rp,sp,#$S
	bl		__ecp_sm2z256_sqr_mont	// p256_sqr_mont(S, S);

	ldr		$bi,[$ap_real,#32]
	ldp		$a0,$a1,[$ap_real,#64]
	ldp		$a2,$a3,[$ap_real,#64+16]
	add		$bp,$ap_real,#32
	add		$rp,sp,#$tmp0
	bl		__ecp_sm2z256_mul_mont	// p256_mul_mont(tmp0, in_z, in_y);

	mov		$t0,$acc0
	mov		$t1,$acc1
	 ldp	$a0,$a1,[sp,#$S]	// forward load for p256_sqr_mont
	mov		$t2,$acc2
	mov		$t3,$acc3
	 ldp	$a2,$a3,[sp,#$S+16]
	add		$rp,$rp_real,#64
	bl		__ecp_sm2z256_add	// p256_mul_by_2(res_z, tmp0);

	add		$rp,sp,#$tmp0
	bl		__ecp_sm2z256_sqr_mont	// p256_sqr_mont(tmp0, S);

	 ldr	$bi,[sp,#$Zsqr]		// forward load for p256_mul_mont
	 ldp	$a0,$a1,[sp,#$M]
	 ldp	$a2,$a3,[sp,#$M+16]
	add		$rp,$rp_real,#32
	bl		__ecp_sm2z256_div_by_2	// p256_div_by_2(res_y, tmp0);

	add		$bp,sp,#$Zsqr
	add		$rp,sp,#$M
	bl		__ecp_sm2z256_mul_mont	// p256_mul_mont(M, M, Zsqr);

	mov	$t0,$acc0		// duplicate M
	mov	$t1,$acc1
	mov	$t2,$acc2
	mov	$t3,$acc3
	mov	$a0,$acc0		// put M aside
	mov	$a1,$acc1
	mov	$a2,$acc2
	mov	$a3,$acc3
	add	$rp,sp,#$M
	bl	__ecp_sm2z256_add
	mov	$t0,$a0			// restore M
	mov	$t1,$a1
	 ldr	$bi,[$ap_real]		// forward load for p256_mul_mont
	mov	$t2,$a2
	 ldp	$a0,$a1,[sp,#$S]
	mov	$t3,$a3
	 ldp	$a2,$a3,[sp,#$S+16]
	bl	__ecp_sm2z256_add	// p256_mul_by_3(M, M);

	add	$bp,$ap_real,#0
	add	$rp,sp,#$S
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S, S, in_x);

	mov	$t0,$acc0
	mov	$t1,$acc1
	 ldp	$a0,$a1,[sp,#$M]	// forward load for p256_sqr_mont
	mov	$t2,$acc2
	mov	$t3,$acc3
	 ldp	$a2,$a3,[sp,#$M+16]
	add	$rp,sp,#$tmp0
	bl	__ecp_sm2z256_add	// p256_mul_by_2(tmp0, S);

	add	$rp,$rp_real,#0
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(res_x, M);

	add	$bp,sp,#$tmp0
	bl	__ecp_sm2z256_sub_from	// p256_sub(res_x, res_x, tmp0);

	add	$bp,sp,#$S
	add	$rp,sp,#$S
	bl	__ecp_sm2z256_sub_morf	// p256_sub(S, S, res_x);

	ldr	$bi,[sp,#$M]
	mov	$a0,$acc0		// copy S
	mov	$a1,$acc1
	mov	$a2,$acc2
	mov	$a3,$acc3
	add	$bp,sp,#$M
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S, S, M);

	add	$bp,$rp_real,#32
	add	$rp,$rp_real,#32
	bl	__ecp_sm2z256_sub_from	// p256_sub(res_y, S, res_y);

	add	sp,x29,#0		// destroy frame
	ldp	x19,x20,[x29,#16]
	ldp	x21,x22,[x29,#32]
	ldp	x29,x30,[sp],#96
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_point_double,.-ecp_sm2z256_point_double
___
}

########################################################################
# void ecp_sm2z256_point_add(P256_POINT *out,const P256_POINT *in1,
#			      const P256_POINT *in2);
{
my ($res_x,$res_y,$res_z,
    $H,$Hsqr,$R,$Rsqr,$Hcub,
    $U1,$U2,$S1,$S2)=map(32*$_,(0..11));
my ($Z1sqr, $Z2sqr) = ($Hsqr, $Rsqr);
# above map() describes stack layout with 12 temporary
# 256-bit vectors on top.
my ($rp_real,$ap_real,$bp_real,$in1infty,$in2infty,$temp0,$temp1,$temp2)=map("x$_",(21..28));

$code.=<<___;
.globl	ecp_sm2z256_point_add
.type	ecp_sm2z256_point_add,%function
.align	5
ecp_sm2z256_point_add:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-96]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	stp	x23,x24,[sp,#48]
	stp	x25,x26,[sp,#64]
	stp	x27,x28,[sp,#80]
	sub	sp,sp,#32*12

	ldp	$a0,$a1,[$bp,#64]	// in2_z
	ldp	$a2,$a3,[$bp,#64+16]
	 mov	$rp_real,$rp
	 mov	$ap_real,$ap
	 mov	$bp_real,$bp
	 ldr	$poly1,.Lpoly+8
	 ldr	$poly3,.Lpoly+24
	orr	$t0,$a0,$a1
	orr	$t2,$a2,$a3
	orr	$in2infty,$t0,$t2
	cmp	$in2infty,#0
	csetm	$in2infty,ne		// ~in2infty
	add	$rp,sp,#$Z2sqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Z2sqr, in2_z);

	ldp	$a0,$a1,[$ap_real,#64]	// in1_z
	ldp	$a2,$a3,[$ap_real,#64+16]
	orr	$t0,$a0,$a1
	orr	$t2,$a2,$a3
	orr	$in1infty,$t0,$t2
	cmp	$in1infty,#0
	csetm	$in1infty,ne		// ~in1infty
	add	$rp,sp,#$Z1sqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Z1sqr, in1_z);

	ldr	$bi,[$bp_real,#64]
	ldp	$a0,$a1,[sp,#$Z2sqr]
	ldp	$a2,$a3,[sp,#$Z2sqr+16]
	add	$bp,$bp_real,#64
	add	$rp,sp,#$S1
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S1, Z2sqr, in2_z);

	ldr	$bi,[$ap_real,#64]
	ldp	$a0,$a1,[sp,#$Z1sqr]
	ldp	$a2,$a3,[sp,#$Z1sqr+16]
	add	$bp,$ap_real,#64
	add	$rp,sp,#$S2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S2, Z1sqr, in1_z);

	ldr	$bi,[$ap_real,#32]
	ldp	$a0,$a1,[sp,#$S1]
	ldp	$a2,$a3,[sp,#$S1+16]
	add	$bp,$ap_real,#32
	add	$rp,sp,#$S1
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S1, S1, in1_y);

	ldr	$bi,[$bp_real,#32]
	ldp	$a0,$a1,[sp,#$S2]
	ldp	$a2,$a3,[sp,#$S2+16]
	add	$bp,$bp_real,#32
	add	$rp,sp,#$S2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S2, S2, in2_y);

	add	$bp,sp,#$S1
	 ldr	$bi,[sp,#$Z2sqr]	// forward load for p256_mul_mont
	 ldp	$a0,$a1,[$ap_real]
	 ldp	$a2,$a3,[$ap_real,#16]
	add	$rp,sp,#$R
	bl	__ecp_sm2z256_sub_from	// p256_sub(R, S2, S1);

	orr	$acc0,$acc0,$acc1	// see if result is zero
	orr	$acc2,$acc2,$acc3
	orr	$temp0,$acc0,$acc2	// ~is_equal(S1,S2)

	add	$bp,sp,#$Z2sqr
	add	$rp,sp,#$U1
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(U1, in1_x, Z2sqr);

	ldr	$bi,[sp,#$Z1sqr]
	ldp	$a0,$a1,[$bp_real]
	ldp	$a2,$a3,[$bp_real,#16]
	add	$bp,sp,#$Z1sqr
	add	$rp,sp,#$U2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(U2, in2_x, Z1sqr);

	add	$bp,sp,#$U1
	 ldp	$a0,$a1,[sp,#$R]	// forward load for p256_sqr_mont
	 ldp	$a2,$a3,[sp,#$R+16]
	add	$rp,sp,#$H
	bl	__ecp_sm2z256_sub_from	// p256_sub(H, U2, U1);

	orr	$acc0,$acc0,$acc1	// see if result is zero
	orr	$acc2,$acc2,$acc3
	orr	$acc0,$acc0,$acc2	// ~is_equal(U1,U2)

	mvn	$temp1,$in1infty	// -1/0 -> 0/-1
	mvn	$temp2,$in2infty	// -1/0 -> 0/-1
	orr	$acc0,$acc0,$temp1
	orr	$acc0,$acc0,$temp2
	orr	$acc0,$acc0,$temp0
	cbnz	$acc0,.Ladd_proceed	// if(~is_equal(U1,U2) | in1infty | in2infty | ~is_equal(S1,S2))

.Ladd_double:
	mov	$ap,$ap_real
	mov	$rp,$rp_real
	ldp	x23,x24,[x29,#48]
	ldp	x25,x26,[x29,#64]
	ldp	x27,x28,[x29,#80]
	add	sp,sp,#32*(12-4)	// difference in stack frames
	b	.Ldouble_shortcut

.align	4
.Ladd_proceed:
	add	$rp,sp,#$Rsqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Rsqr, R);

	ldr	$bi,[$ap_real,#64]
	ldp	$a0,$a1,[sp,#$H]
	ldp	$a2,$a3,[sp,#$H+16]
	add	$bp,$ap_real,#64
	add	$rp,sp,#$res_z
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(res_z, H, in1_z);

	ldp	$a0,$a1,[sp,#$H]
	ldp	$a2,$a3,[sp,#$H+16]
	add	$rp,sp,#$Hsqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Hsqr, H);

	ldr	$bi,[$bp_real,#64]
	ldp	$a0,$a1,[sp,#$res_z]
	ldp	$a2,$a3,[sp,#$res_z+16]
	add	$bp,$bp_real,#64
	add	$rp,sp,#$res_z
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(res_z, res_z, in2_z);

	ldr	$bi,[sp,#$H]
	ldp	$a0,$a1,[sp,#$Hsqr]
	ldp	$a2,$a3,[sp,#$Hsqr+16]
	add	$bp,sp,#$H
	add	$rp,sp,#$Hcub
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(Hcub, Hsqr, H);

	ldr	$bi,[sp,#$Hsqr]
	ldp	$a0,$a1,[sp,#$U1]
	ldp	$a2,$a3,[sp,#$U1+16]
	add	$bp,sp,#$Hsqr
	add	$rp,sp,#$U2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(U2, U1, Hsqr);

	mov	$t0,$acc0
	mov	$t1,$acc1
	mov	$t2,$acc2
	mov	$t3,$acc3
	add	$rp,sp,#$Hsqr
	bl	__ecp_sm2z256_add	// p256_mul_by_2(Hsqr, U2);

	add	$bp,sp,#$Rsqr
	add	$rp,sp,#$res_x
	bl	__ecp_sm2z256_sub_morf	// p256_sub(res_x, Rsqr, Hsqr);

	add	$bp,sp,#$Hcub
	bl	__ecp_sm2z256_sub_from	//  p256_sub(res_x, res_x, Hcub);

	add	$bp,sp,#$U2
	 ldr	$bi,[sp,#$Hcub]		// forward load for p256_mul_mont
	 ldp	$a0,$a1,[sp,#$S1]
	 ldp	$a2,$a3,[sp,#$S1+16]
	add	$rp,sp,#$res_y
	bl	__ecp_sm2z256_sub_morf	// p256_sub(res_y, U2, res_x);

	add	$bp,sp,#$Hcub
	add	$rp,sp,#$S2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S2, S1, Hcub);

	ldr	$bi,[sp,#$R]
	ldp	$a0,$a1,[sp,#$res_y]
	ldp	$a2,$a3,[sp,#$res_y+16]
	add	$bp,sp,#$R
	add	$rp,sp,#$res_y
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(res_y, res_y, R);

	add	$bp,sp,#$S2
	bl	__ecp_sm2z256_sub_from	// p256_sub(res_y, res_y, S2);

	ldp	$a0,$a1,[sp,#$res_x]		// res
	ldp	$a2,$a3,[sp,#$res_x+16]
	ldp	$t0,$t1,[$bp_real]		// in2
	ldp	$t2,$t3,[$bp_real,#16]
___
for($i=0;$i<64;$i+=32) {		# conditional moves
$code.=<<___;
	ldp	$acc0,$acc1,[$ap_real,#$i]	// in1
	cmp	$in1infty,#0			// ~$in1intfy, remember?
	ldp	$acc2,$acc3,[$ap_real,#$i+16]
	csel	$t0,$a0,$t0,ne
	csel	$t1,$a1,$t1,ne
	ldp	$a0,$a1,[sp,#$res_x+$i+32]	// res
	csel	$t2,$a2,$t2,ne
	csel	$t3,$a3,$t3,ne
	cmp	$in2infty,#0			// ~$in2intfy, remember?
	ldp	$a2,$a3,[sp,#$res_x+$i+48]
	csel	$acc0,$t0,$acc0,ne
	csel	$acc1,$t1,$acc1,ne
	ldp	$t0,$t1,[$bp_real,#$i+32]	// in2
	csel	$acc2,$t2,$acc2,ne
	csel	$acc3,$t3,$acc3,ne
	ldp	$t2,$t3,[$bp_real,#$i+48]
	stp	$acc0,$acc1,[$rp_real,#$i]
	stp	$acc2,$acc3,[$rp_real,#$i+16]
___
}
$code.=<<___;
	ldp	$acc0,$acc1,[$ap_real,#$i]	// in1
	cmp	$in1infty,#0			// ~$in1intfy, remember?
	ldp	$acc2,$acc3,[$ap_real,#$i+16]
	csel	$t0,$a0,$t0,ne
	csel	$t1,$a1,$t1,ne
	csel	$t2,$a2,$t2,ne
	csel	$t3,$a3,$t3,ne
	cmp	$in2infty,#0			// ~$in2intfy, remember?
	csel	$acc0,$t0,$acc0,ne
	csel	$acc1,$t1,$acc1,ne
	csel	$acc2,$t2,$acc2,ne
	csel	$acc3,$t3,$acc3,ne
	stp	$acc0,$acc1,[$rp_real,#$i]
	stp	$acc2,$acc3,[$rp_real,#$i+16]

.Ladd_done:
	add	sp,x29,#0		// destroy frame
	ldp	x19,x20,[x29,#16]
	ldp	x21,x22,[x29,#32]
	ldp	x23,x24,[x29,#48]
	ldp	x25,x26,[x29,#64]
	ldp	x27,x28,[x29,#80]
	ldp	x29,x30,[sp],#96
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_point_add,.-ecp_sm2z256_point_add
___
}

########################################################################
# void ecp_sm2z256_point_add_affine(P256_POINT *out,const P256_POINT *in1,
#				     const P256_POINT_AFFINE *in2);
{
my ($res_x,$res_y,$res_z,
    $U2,$S2,$H,$R,$Hsqr,$Hcub,$Rsqr)=map(32*$_,(0..9));
my $Z1sqr = $S2;
# above map() describes stack layout with 10 temporary
# 256-bit vectors on top.
my ($rp_real,$ap_real,$bp_real,$in1infty,$in2infty,$temp)=map("x$_",(21..26));

$code.=<<___;
.globl	ecp_sm2z256_point_add_affine
.type	ecp_sm2z256_point_add_affine,%function
.align	5
ecp_sm2z256_point_add_affine:
	.inst	0xd503233f		// paciasp
	stp	x29,x30,[sp,#-80]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	stp	x23,x24,[sp,#48]
	stp	x25,x26,[sp,#64]
	sub	sp,sp,#32*10

	mov	$rp_real,$rp
	mov	$ap_real,$ap
	mov	$bp_real,$bp
	ldr	$poly1,.Lpoly+8
	ldr	$poly3,.Lpoly+24

	ldp	$a0,$a1,[$ap,#64]	// in1_z
	ldp	$a2,$a3,[$ap,#64+16]
	orr	$t0,$a0,$a1
	orr	$t2,$a2,$a3
	orr	$in1infty,$t0,$t2
	cmp	$in1infty,#0
	csetm	$in1infty,ne		// ~in1infty

	ldp	$acc0,$acc1,[$bp]	// in2_x
	ldp	$acc2,$acc3,[$bp,#16]
	ldp	$t0,$t1,[$bp,#32]	// in2_y
	ldp	$t2,$t3,[$bp,#48]
	orr	$acc0,$acc0,$acc1
	orr	$acc2,$acc2,$acc3
	orr	$t0,$t0,$t1
	orr	$t2,$t2,$t3
	orr	$acc0,$acc0,$acc2
	orr	$t0,$t0,$t2
	orr	$in2infty,$acc0,$t0
	cmp	$in2infty,#0
	csetm	$in2infty,ne		// ~in2infty

	add	$rp,sp,#$Z1sqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Z1sqr, in1_z);

	mov	$a0,$acc0
	mov	$a1,$acc1
	mov	$a2,$acc2
	mov	$a3,$acc3
	ldr	$bi,[$bp_real]
	add	$bp,$bp_real,#0
	add	$rp,sp,#$U2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(U2, Z1sqr, in2_x);

	add	$bp,$ap_real,#0
	 ldr	$bi,[$ap_real,#64]	// forward load for p256_mul_mont
	 ldp	$a0,$a1,[sp,#$Z1sqr]
	 ldp	$a2,$a3,[sp,#$Z1sqr+16]
	add	$rp,sp,#$H
	bl	__ecp_sm2z256_sub_from	// p256_sub(H, U2, in1_x);

	add	$bp,$ap_real,#64
	add	$rp,sp,#$S2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S2, Z1sqr, in1_z);

	ldr	$bi,[$ap_real,#64]
	ldp	$a0,$a1,[sp,#$H]
	ldp	$a2,$a3,[sp,#$H+16]
	add	$bp,$ap_real,#64
	add	$rp,sp,#$res_z
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(res_z, H, in1_z);

	ldr	$bi,[$bp_real,#32]
	ldp	$a0,$a1,[sp,#$S2]
	ldp	$a2,$a3,[sp,#$S2+16]
	add	$bp,$bp_real,#32
	add	$rp,sp,#$S2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S2, S2, in2_y);

	add	$bp,$ap_real,#32
	 ldp	$a0,$a1,[sp,#$H]	// forward load for p256_sqr_mont
	 ldp	$a2,$a3,[sp,#$H+16]
	add	$rp,sp,#$R
	bl	__ecp_sm2z256_sub_from	// p256_sub(R, S2, in1_y);

	add	$rp,sp,#$Hsqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Hsqr, H);

	ldp	$a0,$a1,[sp,#$R]
	ldp	$a2,$a3,[sp,#$R+16]
	add	$rp,sp,#$Rsqr
	bl	__ecp_sm2z256_sqr_mont	// p256_sqr_mont(Rsqr, R);

	ldr	$bi,[sp,#$H]
	ldp	$a0,$a1,[sp,#$Hsqr]
	ldp	$a2,$a3,[sp,#$Hsqr+16]
	add	$bp,sp,#$H
	add	$rp,sp,#$Hcub
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(Hcub, Hsqr, H);

	ldr	$bi,[$ap_real]
	ldp	$a0,$a1,[sp,#$Hsqr]
	ldp	$a2,$a3,[sp,#$Hsqr+16]
	add	$bp,$ap_real,#0
	add	$rp,sp,#$U2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(U2, in1_x, Hsqr);

	mov	$t0,$acc0
	mov	$t1,$acc1
	mov	$t2,$acc2
	mov	$t3,$acc3
	add	$rp,sp,#$Hsqr
	bl	__ecp_sm2z256_add	// p256_mul_by_2(Hsqr, U2);

	add	$bp,sp,#$Rsqr
	add	$rp,sp,#$res_x
	bl	__ecp_sm2z256_sub_morf	// p256_sub(res_x, Rsqr, Hsqr);

	add	$bp,sp,#$Hcub
	bl	__ecp_sm2z256_sub_from	//  p256_sub(res_x, res_x, Hcub);

	add	$bp,sp,#$U2
	 ldr	$bi,[$ap_real,#32]	// forward load for p256_mul_mont
	 ldp	$a0,$a1,[sp,#$Hcub]
	 ldp	$a2,$a3,[sp,#$Hcub+16]
	add	$rp,sp,#$res_y
	bl	__ecp_sm2z256_sub_morf	// p256_sub(res_y, U2, res_x);

	add	$bp,$ap_real,#32
	add	$rp,sp,#$S2
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(S2, in1_y, Hcub);

	ldr	$bi,[sp,#$R]
	ldp	$a0,$a1,[sp,#$res_y]
	ldp	$a2,$a3,[sp,#$res_y+16]
	add	$bp,sp,#$R
	add	$rp,sp,#$res_y
	bl	__ecp_sm2z256_mul_mont	// p256_mul_mont(res_y, res_y, R);

	add	$bp,sp,#$S2
	bl	__ecp_sm2z256_sub_from	// p256_sub(res_y, res_y, S2);

	ldp	$a0,$a1,[sp,#$res_x]		// res
	ldp	$a2,$a3,[sp,#$res_x+16]
	ldp	$t0,$t1,[$bp_real]		// in2
	ldp	$t2,$t3,[$bp_real,#16]
___
for($i=0;$i<64;$i+=32) {		# conditional moves
$code.=<<___;
	ldp	$acc0,$acc1,[$ap_real,#$i]	// in1
	cmp	$in1infty,#0			// ~$in1intfy, remember?
	ldp	$acc2,$acc3,[$ap_real,#$i+16]
	csel	$t0,$a0,$t0,ne
	csel	$t1,$a1,$t1,ne
	ldp	$a0,$a1,[sp,#$res_x+$i+32]	// res
	csel	$t2,$a2,$t2,ne
	csel	$t3,$a3,$t3,ne
	cmp	$in2infty,#0			// ~$in2intfy, remember?
	ldp	$a2,$a3,[sp,#$res_x+$i+48]
	csel	$acc0,$t0,$acc0,ne
	csel	$acc1,$t1,$acc1,ne
	ldp	$t0,$t1,[$bp_real,#$i+32]	// in2
	csel	$acc2,$t2,$acc2,ne
	csel	$acc3,$t3,$acc3,ne
	ldp	$t2,$t3,[$bp_real,#$i+48]
	stp	$acc0,$acc1,[$rp_real,#$i]
	stp	$acc2,$acc3,[$rp_real,#$i+16]
___
$code.=<<___	if ($i == 0);
	adr	$bp_real,.Lone_mont-64
___
}
$code.=<<___;
	ldp	$acc0,$acc1,[$ap_real,#$i]	// in1
	cmp	$in1infty,#0			// ~$in1intfy, remember?
	ldp	$acc2,$acc3,[$ap_real,#$i+16]
	csel	$t0,$a0,$t0,ne
	csel	$t1,$a1,$t1,ne
	csel	$t2,$a2,$t2,ne
	csel	$t3,$a3,$t3,ne
	cmp	$in2infty,#0			// ~$in2intfy, remember?
	csel	$acc0,$t0,$acc0,ne
	csel	$acc1,$t1,$acc1,ne
	csel	$acc2,$t2,$acc2,ne
	csel	$acc3,$t3,$acc3,ne
	stp	$acc0,$acc1,[$rp_real,#$i]
	stp	$acc2,$acc3,[$rp_real,#$i+16]

	add	sp,x29,#0		// destroy frame
	ldp	x19,x20,[x29,#16]
	ldp	x21,x22,[x29,#32]
	ldp	x23,x24,[x29,#48]
	ldp	x25,x26,[x29,#64]
	ldp	x29,x30,[sp],#80
	.inst	0xd50323bf		// autiasp
	ret
.size	ecp_sm2z256_point_add_affine,.-ecp_sm2z256_point_add_affine
___
}

if (1) {
my ($ord0,$ord1,$ord2,$ord3) = ($poly1,$poly3,$bp,$bi);
$code.=<<___;
////////////////////////////////////////////////////////////////////////
// void ecp_sm2z256_ord_sub_reduce(uint64_t res[4], uint64_t a[4]);
// if a>ord then res=a-ord. else res=a
.globl	ecp_sm2z256_ord_sub_reduce
.type	ecp_sm2z256_ord_sub_reduce,%function
.align	4
ecp_sm2z256_ord_sub_reduce:
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	// load input and order
	adr		$t0,.Lord
	ldp		$a0,$a1,[$ap]
	ldp		$a2,$a3,[$ap,#16]
	ldp		$ord0,$ord1,[$t0,#0]
	ldp		$ord2,$ord3,[$t0,#16]
	// a-order
	subs	$acc0, $a0, $ord0
	sbcs	$acc1, $a1, $ord1
	sbcs	$acc2, $a2, $ord2
	sbcs	$acc3, $a3, $ord3

	// ret = borrow ? ret : ret-order
	csel	$acc0, $a0, $acc0, lo
	csel	$acc1, $a1, $acc1, lo
	stp		$acc0, $acc1, [$rp]
	csel	$acc2, $a2, $acc2, lo
	csel	$acc3, $a3, $acc3, lo
	stp		$acc2, $acc3, [$rp, #16]
	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	ret
.size	ecp_sm2z256_ord_sub_reduce,.-ecp_sm2z256_ord_sub_reduce
___
}

if (1) {
my ($ord0,$ord1,$ord2,$ord3) = ($poly1,$poly3,$bp,$bi);
$code.=<<___;
////////////////////////////////////////////////////////////////////////
// void ecp_sm2z256_ord_negative(uint64_t res[4], uint64_t a[4]);
// res=order-a suppose a<order
.globl	ecp_sm2z256_ord_negative
.type	ecp_sm2z256_ord_negative,%function
.align	4
ecp_sm2z256_ord_negative:
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	// load input and order
	adr		$t0,.Lord
	ldp		$a0,$a1,[$ap]
	ldp		$a2,$a3,[$ap,#16]
	ldp		$ord0,$ord1,[$t0,#0]
	ldp		$ord2,$ord3,[$t0,#16]
	// order-a
	subs	$a0, $ord0, $a0
	sbcs	$a1, $ord1, $a1
	sbcs	$a2, $ord2, $a2
	sbcs	$a3, $ord3, $a3
	// store
	stp		$a0, $a1, [$rp]
	stp		$a2, $a3, [$rp, #16]
	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	ret
.size	ecp_sm2z256_ord_negative,.-ecp_sm2z256_ord_negative
___
}

if (1) {
my ($ord0,$ord1,$ord2,$ord3) = ($t0,$t1,$t2,$t3);
my ($b0,$b1,$b2,$b3,$a4) = ($poly1,$poly3,$acc3,$acc4,$acc5);
$code.=<<___;
// void ecp_sm2z256_ord_add(uint64_t res[4], uint64_t a[4], uint64_4 b[4]);
// a+=b => if a>ord then res=a-ord. else res=a
.globl	ecp_sm2z256_ord_add
.type	ecp_sm2z256_ord_add,%function
.align	4
ecp_sm2z256_ord_add:
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	// load input and order
	adr		$acc0,.Lord
	ldp		$a0,$a1,[$ap]
	ldp		$a2,$a3,[$ap,#16]
	ldp		$ord0,$ord1,[$acc0,#0]
	ldp		$ord2,$ord3,[$acc0,#16]
	ldp		$b0,$b1,[$bp]
	ldp		$b2,$b3,[$bp,#16]
	// a+b
	adds	$a0,$a0,$b0
	adcs	$a1,$a1,$b1
	adcs 	$a2,$a2,$b2
	adcs	$a3,$a3,$b3
	adc		$a4,xzr,xzr
	// a-order
	subs	$acc0, $a0, $ord0
	sbcs	$acc1, $a1, $ord1
	sbcs	$acc2, $a2, $ord2
	sbcs	$acc3, $a3, $ord3
	sbcs	xzr, $a4, xzr

	// ret = borrow ? ret : ret-order
	csel	$acc0, $a0, $acc0, lo
	csel	$acc1, $a1, $acc1, lo
	stp		$acc0, $acc1, [$rp]
	csel	$acc2, $a2, $acc2, lo
	csel	$acc3, $a3, $acc3, lo
	stp		$acc2, $acc3, [$rp, #16]
	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	ret
.size	ecp_sm2z256_ord_add,.-ecp_sm2z256_ord_add


////////////////////////////////////////////////////////////////////////
// void ecp_sm2z256_ord_sub(uint64_t res[4], uint64_t a[4], uint64_t b[4]);
// res=a-b
.globl	ecp_sm2z256_ord_sub
.type	ecp_sm2z256_ord_sub,%function
.align	4
ecp_sm2z256_ord_sub:
	stp	x29,x30,[sp,#-32]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	// load input and order
	adr		$acc0,.Lord
	ldp		$a0,$a1,[$ap]
	ldp		$a2,$a3,[$ap,#16]
	ldp		$ord0,$ord1,[$acc0,#0]
	ldp		$ord2,$ord3,[$acc0,#16]
	ldp		$b0,$b1,[$bp]
	ldp		$b2,$b3,[$bp,#16]
	// a-b
	subs	$a0,$a0,$b0
	sbcs	$a1,$a1,$b1
	sbcs 	$a2,$a2,$b2
	sbcs	$a3,$a3,$b3
	sbc		$a4,xzr,xzr

	// a+order
	adds	$acc0, $a0, $ord0
	adcs	$acc1, $a1, $ord1
	adcs	$acc2, $a2, $ord2
	adc		$acc3, $a3, $ord3
	// did subtraction borrow?
	cmp		$a4,xzr

	// ret = borrow ? ret+order : ret
	csel	$acc0, $a0, $acc0, eq
	csel	$acc1, $a1, $acc1, eq
	stp		$acc0, $acc1, [$rp]
	csel	$acc2, $a2, $acc2, eq
	csel	$acc3, $a3, $acc3, eq
	stp		$acc2, $acc3, [$rp, #16]
	ldp	x19,x20,[sp,#16]
	ldp	x29,x30,[sp],#32
	ret
.size	ecp_sm2z256_ord_sub,.-ecp_sm2z256_ord_sub
___
}

if (1) {
my ($ord0,$ord1) = ($poly1,$poly3);
my ($ord2,$ord3,$ordk,$t4) = map("x$_",(21..24));
my $acc7 = $bi;

$code.=<<___;
////////////////////////////////////////////////////////////////////////
// void ecp_sm2z256_ord_mul_mont(uint64_t res[4], uint64_t a[4],
//                                uint64_t b[4]);
.globl	ecp_sm2z256_ord_mul_mont
.type	ecp_sm2z256_ord_mul_mont,%function
.align	4
ecp_sm2z256_ord_mul_mont:
	stp		x29,x30,[sp,#-64]!
	add		x29,sp,#0
	stp		x19,x20,[sp,#16]
	stp		x21,x22,[sp,#32]
	stp		x23,x24,[sp,#48]

	adr		$ordk,.Lord
	ldr		$bi,[$bp]		// bp[0]
	ldp		$a0,$a1,[$ap]
	ldp		$a2,$a3,[$ap,#16]

	ldp		$ord0,$ord1,[$ordk,#0]
	ldp		$ord2,$ord3,[$ordk,#16]
	ldr		$ordk,[$ordk,#32]

	mul		$acc0,$a0,$bi		// a[0]*b[0]
	umulh	$t0,$a0,$bi

	mul		$acc1,$a1,$bi		// a[1]*b[0]
	umulh	$t1,$a1,$bi

	mul		$acc2,$a2,$bi		// a[2]*b[0]
	umulh	$t2,$a2,$bi

	mul		$acc3,$a3,$bi		// a[3]*b[0]
	umulh	$acc4,$a3,$bi

	mul		$t4,$acc0,$ordk		// $t4=m=$acc0*ord' mod 2^64

	adds	$acc1,$acc1,$t0		// accumulate high parts of multiplication
	adcs	$acc2,$acc2,$t1
	adcs	$acc3,$acc3,$t2
	adc		$acc4,$acc4,xzr
	mov		$acc5,xzr

	// now {$acc5,$acc4,$acc3,$acc2,$acc1,$acc0} is the accumulated result
___
for ($i=1;$i<4;$i++) {
	################################################################
	#            ffff0000.ffffffff.yyyyyyyy.zzzzzzzz
	# *                                     abcdefgh
	# + xxxxxxxx.xxxxxxxx.xxxxxxxx.xxxxxxxx.xxxxxxxx
	#
	# Now observing that ff..ff*x = (2^n-1)*x = 2^n*x-x, we
	# rewrite above as:
	#
	#   xxxxxxxx.xxxxxxxx.xxxxxxxx.xxxxxxxx.xxxxxxxx
	# - 0000abcd.efgh0000.abcdefgh.00000000.00000000
	# + abcdefgh.abcdefgh.yzayzbyz.cyzdyzey.zfyzgyzh
$code.=<<___;
	ldr		$bi,[$bp,#8*$i]		// b[i]

	lsl		$t0,$t4,#32			// $t0=$t4<<32
	subs	$acc2,$acc2,$t4		// $acc2=$acc2-m
	lsr		$t1,$t4,#32			// $t1=$t4>>32
	sbcs	$acc3,$acc3,$t0		// $acc3=$acc3-(m<<32)
	sbcs	$acc4,$acc4,$t1		// $acc4=$acc4-(m>>32)
	sbc		$acc5,$acc5,xzr		// $acc5-=borrow

	subs	xzr,$acc0,#1		// $acc0-1 and set flag
	umulh	$t1,$ord0,$t4		// $t1=high(ord0*m)
	mul		$t2,$ord1,$t4		// $t2=low(ord1*m)
	umulh	$t3,$ord1,$t4		// $t3=high(ord1*m)

	adcs	$t2,$t2,$t1			// $t2=$t2+$t1+carry
	 mul	$t0,$a0,$bi			// $t0=low($a0*$bi)
	adc		$t3,$t3,xzr			// $t3=$t3+carry
	 mul	$t1,$a1,$bi			// $t1=low($a1*$bi)

	adds	$acc0,$acc1,$t2		// $acc0=$acc1+$t2
	 mul	$t2,$a2,$bi			// $t2=$a2*$bi
	adcs	$acc1,$acc2,$t3		// $acc1=$acc2+$t3
	 mul	$t3,$a3,$bi			// $t3=low($a3*$bi)
	adcs	$acc2,$acc3,xzr		// $acc2=$acc3+carry
	adcs	$acc3,$acc4,$t4		// $acc3=$acc4+$t4
	adc		$acc4,$acc5,xzr		// $acc4=$acc5+carry

	adds	$acc0,$acc0,$t0		// accumulate low parts
	umulh	$t0,$a0,$bi
	adcs	$acc1,$acc1,$t1
	umulh	$t1,$a1,$bi
	adcs	$acc2,$acc2,$t2
	umulh	$t2,$a2,$bi
	adcs	$acc3,$acc3,$t3
	umulh	$t3,$a3,$bi
	adc		$acc4,$acc4,xzr
	mul		$t4,$acc0,$ordk
	adds	$acc1,$acc1,$t0		// accumulate high parts
	adcs	$acc2,$acc2,$t1
	adcs	$acc3,$acc3,$t2
	adcs	$acc4,$acc4,$t3
	adc		$acc5,xzr,xzr
___
}
$code.=<<___;
	lsl		$t0,$t4,#32		// last reduction
	subs	$acc2,$acc2,$t4
	lsr		$t1,$t4,#32
	sbcs	$acc3,$acc3,$t0
	sbcs	$acc4,$acc4,$t1
	sbc		$acc5,$acc5,xzr

	subs	xzr,$acc0,#1
	umulh	$t1,$ord0,$t4
	mul		$t2,$ord1,$t4
	umulh	$t3,$ord1,$t4

	adcs	$t2,$t2,$t1
	adc		$t3,$t3,xzr

	adds	$acc0,$acc1,$t2
	adcs	$acc1,$acc2,$t3
	adcs	$acc2,$acc3,xzr
	adcs	$acc3,$acc4,$t4
	adc		$acc4,$acc5,xzr

	subs	$t0,$acc0,$ord0		// ret -= modulus
	sbcs	$t1,$acc1,$ord1
	sbcs	$t2,$acc2,$ord2
	sbcs	$t3,$acc3,$ord3
	sbcs	xzr,$acc4,xzr

	csel	$acc0,$acc0,$t0,lo	// ret = borrow ? ret : ret-modulus
	csel	$acc1,$acc1,$t1,lo
	csel	$acc2,$acc2,$t2,lo
	stp		$acc0,$acc1,[$rp]
	csel	$acc3,$acc3,$t3,lo
	stp		$acc2,$acc3,[$rp,#16]

	ldp		x19,x20,[sp,#16]
	ldp		x21,x22,[sp,#32]
	ldp		x23,x24,[sp,#48]
	ldr		x29,[sp],#64
	ret
.size	ecp_sm2z256_ord_mul_mont,.-ecp_sm2z256_ord_mul_mont

////////////////////////////////////////////////////////////////////////
// void ecp_sm2z256_ord_sqr_mont(uint64_t res[4], uint64_t a[4],
//                                uint64_t rep);
.globl	ecp_sm2z256_ord_sqr_mont
.type	ecp_sm2z256_ord_sqr_mont,%function
.align	4
ecp_sm2z256_ord_sqr_mont:
	stp	x29,x30,[sp,#-64]!
	add	x29,sp,#0
	stp	x19,x20,[sp,#16]
	stp	x21,x22,[sp,#32]
	stp	x23,x24,[sp,#48]

	adr	$ordk,.Lord
	ldp	$a0,$a1,[$ap]
	ldp	$a2,$a3,[$ap,#16]

	ldp	$ord0,$ord1,[$ordk,#0]
	ldp	$ord2,$ord3,[$ordk,#16]
	ldr	$ordk,[$ordk,#32]
	b	.Loop_ord_sqr

.align	4
.Loop_ord_sqr:
	sub	$bp,$bp,#1
	////////////////////////////////////////////////////////////////
	//  |  |  |  |  |  |a1*a0|  |
	//  |  |  |  |  |a2*a0|  |  |
	//  |  |a3*a2|a3*a0|  |  |  |
	//  |  |  |  |a2*a1|  |  |  |
	//  |  |  |a3*a1|  |  |  |  |
	// *|  |  |  |  |  |  |  | 2|
	// +|a3*a3|a2*a2|a1*a1|a0*a0|
	//  |--+--+--+--+--+--+--+--|
	//  |A7|A6|A5|A4|A3|A2|A1|A0|, where Ax is $accx, i.e. follow $accx
	//
	//  "can't overflow" below mark carrying into high part of
	//  multiplication result, which can't overflow, because it
	//  can never be all ones.

	mul		$acc1,$a1,$a0		// a[1]*a[0]
	umulh	$t1,$a1,$a0
	mul		$acc2,$a2,$a0		// a[2]*a[0]
	umulh	$t2,$a2,$a0
	mul		$acc3,$a3,$a0		// a[3]*a[0]
	umulh	$acc4,$a3,$a0

	adds	$acc2,$acc2,$t1		// accumulate high parts of multiplication
	 mul	$t0,$a2,$a1		// a[2]*a[1]
	 umulh	$t1,$a2,$a1
	adcs	$acc3,$acc3,$t2
	 mul	$t2,$a3,$a1		// a[3]*a[1]
	 umulh	$t3,$a3,$a1
	adc		$acc4,$acc4,xzr		// can't overflow

	mul		$acc5,$a3,$a2		// a[3]*a[2]
	umulh	$acc6,$a3,$a2

	adds	$t1,$t1,$t2		// accumulate high parts of multiplication
	 mul	$acc0,$a0,$a0		// a[0]*a[0]
	adc		$t2,$t3,xzr		// can't overflow

	adds	$acc3,$acc3,$t0		// accumulate low parts of multiplication
	 umulh	$a0,$a0,$a0
	adcs	$acc4,$acc4,$t1
	 mul	$t1,$a1,$a1		// a[1]*a[1]
	adcs	$acc5,$acc5,$t2
	 umulh	$a1,$a1,$a1
	adc		$acc6,$acc6,xzr		// can't overflow

	adds	$acc1,$acc1,$acc1	// acc[1-6]*=2
	 mul	$t2,$a2,$a2		// a[2]*a[2]
	adcs	$acc2,$acc2,$acc2
	 umulh	$a2,$a2,$a2
	adcs	$acc3,$acc3,$acc3
	 mul	$t3,$a3,$a3		// a[3]*a[3]
	adcs	$acc4,$acc4,$acc4
	 umulh	$a3,$a3,$a3
	adcs	$acc5,$acc5,$acc5
	adcs	$acc6,$acc6,$acc6
	adc		$acc7,xzr,xzr

	adds	$acc1,$acc1,$a0		// +a[i]*a[i]
	 mul	$t4,$acc0,$ordk
	adcs	$acc2,$acc2,$t1
	adcs	$acc3,$acc3,$a1
	adcs	$acc4,$acc4,$t2
	adcs	$acc5,$acc5,$a2
	adcs	$acc6,$acc6,$t3
	adc		$acc7,$acc7,$a3
___
for($i=0; $i<4; $i++) {			# reductions
$code.=<<___;
	subs	xzr,$acc0,#1
	umulh	$t1,$ord0,$t4
	mul		$t2,$ord1,$t4
	umulh	$t3,$ord1,$t4

	adcs	$t2,$t2,$t1
	adc		$t3,$t3,xzr

	adds	$acc0,$acc1,$t2
	adcs	$acc1,$acc2,$t3
	adcs	$acc2,$acc3,xzr
	adc		$acc3,xzr,$t4		// can't overflow
___
$code.=<<___	if ($i<3);
	mul	$t3,$acc0,$ordk
___
$code.=<<___;
	lsl		$t0,$t4,#32
	subs	$acc1,$acc1,$t4
	lsr		$t1,$t4,#32
	sbcs	$acc2,$acc2,$t0
	sbc		$acc3,$acc3,$t1		// can't borrow
___
	($t3,$t4) = ($t4,$t3);
}
$code.=<<___;
	adds	$acc0,$acc0,$acc4	// accumulate upper half
	adcs	$acc1,$acc1,$acc5
	adcs	$acc2,$acc2,$acc6
	adcs	$acc3,$acc3,$acc7
	adc		$acc4,xzr,xzr

	subs	$t0,$acc0,$ord0		// ret -= modulus
	sbcs	$t1,$acc1,$ord1
	sbcs	$t2,$acc2,$ord2
	sbcs	$t3,$acc3,$ord3
	sbcs	xzr,$acc4,xzr

	csel	$a0,$acc0,$t0,lo	// ret = borrow ? ret : ret-modulus
	csel	$a1,$acc1,$t1,lo
	csel	$a2,$acc2,$t2,lo
	csel	$a3,$acc3,$t3,lo

	cbnz	$bp,.Loop_ord_sqr

	stp	$a0,$a1,[$rp]
	stp	$a2,$a3,[$rp,#16]

	ldp	x19,x20,[sp,#16]
	ldp	x21,x22,[sp,#32]
	ldp	x23,x24,[sp,#48]
	ldr	x29,[sp],#64
	ret
.size	ecp_sm2z256_ord_sqr_mont,.-ecp_sm2z256_ord_sqr_mont
___
}	}

########################################################################
# scatter-gather subroutines
if($gather_scatter_use_neon == 0)
{
my ($out,$inp,$index,$mask)=map("x$_",(0..3));
$code.=<<___;
// void	ecp_sm2z256_scatter_w5(void *x0,const P256_POINT *x1,
//					 int x2);
.globl	ecp_sm2z256_scatter_w5
.type	ecp_sm2z256_scatter_w5,%function
.align	4
ecp_sm2z256_scatter_w5:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	add	$out,$out,$index,lsl#2

	ldp	x4,x5,[$inp]		// X
	ldp	x6,x7,[$inp,#16]
	stur	w4,[$out,#64*0-4]
	lsr	x4,x4,#32
	str	w5,[$out,#64*1-4]
	lsr	x5,x5,#32
	str	w6,[$out,#64*2-4]
	lsr	x6,x6,#32
	str	w7,[$out,#64*3-4]
	lsr	x7,x7,#32
	str	w4,[$out,#64*4-4]
	str	w5,[$out,#64*5-4]
	str	w6,[$out,#64*6-4]
	str	w7,[$out,#64*7-4]
	add	$out,$out,#64*8

	ldp	x4,x5,[$inp,#32]	// Y
	ldp	x6,x7,[$inp,#48]
	stur	w4,[$out,#64*0-4]
	lsr	x4,x4,#32
	str	w5,[$out,#64*1-4]
	lsr	x5,x5,#32
	str	w6,[$out,#64*2-4]
	lsr	x6,x6,#32
	str	w7,[$out,#64*3-4]
	lsr	x7,x7,#32
	str	w4,[$out,#64*4-4]
	str	w5,[$out,#64*5-4]
	str	w6,[$out,#64*6-4]
	str	w7,[$out,#64*7-4]
	add	$out,$out,#64*8

	ldp	x4,x5,[$inp,#64]	// Z
	ldp	x6,x7,[$inp,#80]
	stur	w4,[$out,#64*0-4]
	lsr	x4,x4,#32
	str	w5,[$out,#64*1-4]
	lsr	x5,x5,#32
	str	w6,[$out,#64*2-4]
	lsr	x6,x6,#32
	str	w7,[$out,#64*3-4]
	lsr	x7,x7,#32
	str	w4,[$out,#64*4-4]
	str	w5,[$out,#64*5-4]
	str	w6,[$out,#64*6-4]
	str	w7,[$out,#64*7-4]

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_scatter_w5,.-ecp_sm2z256_scatter_w5

// void	ecp_sm2z256_gather_w5(P256_POINT *x0,const void *x1,
//					      int x2);
.globl	ecp_sm2z256_gather_w5
.type	ecp_sm2z256_gather_w5,%function
.align	4
ecp_sm2z256_gather_w5:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	cmp	$index,xzr
	csetm	x3,ne
	add	$index,$index,x3
	add	$inp,$inp,$index,lsl#2

	ldr	w4,[$inp,#64*0]
	ldr	w5,[$inp,#64*1]
	ldr	w6,[$inp,#64*2]
	ldr	w7,[$inp,#64*3]
	ldr	w8,[$inp,#64*4]
	ldr	w9,[$inp,#64*5]
	ldr	w10,[$inp,#64*6]
	ldr	w11,[$inp,#64*7]
	add	$inp,$inp,#64*8
	orr	x4,x4,x8,lsl#32
	orr	x5,x5,x9,lsl#32
	orr	x6,x6,x10,lsl#32
	orr	x7,x7,x11,lsl#32
	csel	x4,x4,xzr,ne
	csel	x5,x5,xzr,ne
	csel	x6,x6,xzr,ne
	csel	x7,x7,xzr,ne
	stp	x4,x5,[$out]		// X
	stp	x6,x7,[$out,#16]

	ldr	w4,[$inp,#64*0]
	ldr	w5,[$inp,#64*1]
	ldr	w6,[$inp,#64*2]
	ldr	w7,[$inp,#64*3]
	ldr	w8,[$inp,#64*4]
	ldr	w9,[$inp,#64*5]
	ldr	w10,[$inp,#64*6]
	ldr	w11,[$inp,#64*7]
	add	$inp,$inp,#64*8
	orr	x4,x4,x8,lsl#32
	orr	x5,x5,x9,lsl#32
	orr	x6,x6,x10,lsl#32
	orr	x7,x7,x11,lsl#32
	csel	x4,x4,xzr,ne
	csel	x5,x5,xzr,ne
	csel	x6,x6,xzr,ne
	csel	x7,x7,xzr,ne
	stp	x4,x5,[$out,#32]	// Y
	stp	x6,x7,[$out,#48]

	ldr	w4,[$inp,#64*0]
	ldr	w5,[$inp,#64*1]
	ldr	w6,[$inp,#64*2]
	ldr	w7,[$inp,#64*3]
	ldr	w8,[$inp,#64*4]
	ldr	w9,[$inp,#64*5]
	ldr	w10,[$inp,#64*6]
	ldr	w11,[$inp,#64*7]
	orr	x4,x4,x8,lsl#32
	orr	x5,x5,x9,lsl#32
	orr	x6,x6,x10,lsl#32
	orr	x7,x7,x11,lsl#32
	csel	x4,x4,xzr,ne
	csel	x5,x5,xzr,ne
	csel	x6,x6,xzr,ne
	csel	x7,x7,xzr,ne
	stp	x4,x5,[$out,#64]	// Z
	stp	x6,x7,[$out,#80]

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_gather_w5,.-ecp_sm2z256_gather_w5

// void	ecp_sm2z256_scatter_w7(void *x0,const P256_POINT_AFFINE *x1,
//					 int x2);
.globl	ecp_sm2z256_scatter_w7
.type	ecp_sm2z256_scatter_w7,%function
.align	4
ecp_sm2z256_scatter_w7:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0
	add	$out,$out,$index
	// loop num = 8
	mov	$index,#64/8
// each loop handle 8B, 1 point = 64B, so loop num = 8
.Loop_scatter_w7:
	// load 64-bit from $inp and update $inp
	ldr	x3,[$inp],#8
	subs	$index,$index,#1
	prfm	pstl1strm,[$out,#4096+64*0]
	prfm	pstl1strm,[$out,#4096+64*1]
	prfm	pstl1strm,[$out,#4096+64*2]
	prfm	pstl1strm,[$out,#4096+64*3]
	prfm	pstl1strm,[$out,#4096+64*4]
	prfm	pstl1strm,[$out,#4096+64*5]
	prfm	pstl1strm,[$out,#4096+64*6]
	prfm	pstl1strm,[$out,#4096+64*7]
	// put the i-th Byte
	strb	w3,[$out,#64*0]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*1]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*2]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*3]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*4]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*5]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*6]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*7]
	add	$out,$out,#64*8
	b.ne	.Loop_scatter_w7

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_scatter_w7,.-ecp_sm2z256_scatter_w7

// void ecp_sm2z256_gather_w7(P256_POINT_AFFINE *val,
//                            const P256_POINT_AFFINE *in_t, int idx);
.globl	ecp_sm2z256_gather_w7
.type	ecp_sm2z256_gather_w7,%function
.align	4
ecp_sm2z256_gather_w7:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	cmp	$index,xzr
	// Conditional Set Mask sets all bits of the destination register to 1
	// if the condition is TRUE, and otherwise sets all bits to 0.
	// i.e. if $index!=0 then x3=0xff...ff
	csetm	x3,ne
	// if $index=1, $index=1+0xff...ff=0
	add	$index,$index,x3
	// if $index=1 $inp=$inp+1
	add	$inp,$inp,$index
	// $index = 8, loop repeats 8 times
	mov	$index,#64/8
	nop
// ldrb: load a byte with zero-extended
// prfm pldl1strm, pld: prefetch for load; l1: level 1 cache; 
// strm: for data that is used only once
// this loop loads 8 bytes = 1 64-bit from [$inp,#64*0]-[$inp,#64*7] each time
// this loop loads 8*64-bit overall
// prefetch for load [#4096+64*0]-[#4096+64*7]
.Loop_gather_w7:
	ldrb	w4,[$inp,#64*0]
	prfm	pldl1strm,[$inp,#4096+64*0]
	// loop control
	subs	$index,$index,#1
	ldrb	w5,[$inp,#64*1]
	prfm	pldl1strm,[$inp,#4096+64*1]
	ldrb	w6,[$inp,#64*2]
	prfm	pldl1strm,[$inp,#4096+64*2]
	ldrb	w7,[$inp,#64*3]
	prfm	pldl1strm,[$inp,#4096+64*3]
	ldrb	w8,[$inp,#64*4]
	prfm	pldl1strm,[$inp,#4096+64*4]
	ldrb	w9,[$inp,#64*5]
	prfm	pldl1strm,[$inp,#4096+64*5]
	ldrb	w10,[$inp,#64*6]
	prfm	pldl1strm,[$inp,#4096+64*6]
	ldrb	w11,[$inp,#64*7]
	prfm	pldl1strm,[$inp,#4096+64*7]
	// $inp+=512
	add	$inp,$inp,#64*8
	// concat 8 8-bit into 1 64-bit 
	orr	x4,x4,x5,lsl#8
	orr	x6,x6,x7,lsl#8
	orr	x8,x8,x9,lsl#8
	orr	x4,x4,x6,lsl#16
	orr	x10,x10,x11,lsl#8
	orr	x4,x4,x8,lsl#32
	orr	x4,x4,x10,lsl#48
	// if $index=0, output=0
	and	x4,x4,x3
	// store the 64-bit value
	str	x4,[$out],#8
	b.ne	.Loop_gather_w7

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_gather_w7,.-ecp_sm2z256_gather_w7

// void	ecp_sm2z256_scatter_w6(void *x0,const P256_POINT *x1,
//					 int x2);
.globl	ecp_sm2z256_scatter_w6
.type	ecp_sm2z256_scatter_w6,%function
.align	4
ecp_sm2z256_scatter_w6:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	sub $index,$index,#1
	// +$index*2, because the basic item is 16-bit
	add	$out,$out,$index,lsl#1

	// each loop handle 16B, 1 point = 96B, 96/16=6
	mov $index,#96/16
.Loop_scatter_w6:
	ldp x3, x4, [$inp], #16
	subs $index,$index,#1
	strh w3,[$out,#64*0]
	lsr x3,x3,#16
	strh w3,[$out,#64*1]
	lsr x3,x3,#16
	strh w3,[$out,#64*2]
	lsr x3,x3,#16
	strh w3,[$out,#64*3]

	strh w4,[$out,#64*4]
	lsr x4,x4,#16
	strh w4,[$out,#64*5]
	lsr x4,x4,#16
	strh w4,[$out,#64*6]
	lsr x4,x4,#16
	strh w4,[$out,#64*7]
	add $out,$out,#64*8
	b.ne .Loop_scatter_w6

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_scatter_w6,.-ecp_sm2z256_scatter_w6

// void ecp_sm2z256_gather_w6(P256_POINT_AFFINE *val,
//                            const P256_POINT_AFFINE *in_t, int idx);
.globl	ecp_sm2z256_gather_w6
.type	ecp_sm2z256_gather_w6,%function
.align	4
ecp_sm2z256_gather_w6:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	cmp	$index,xzr
	csetm	x3,ne
	add	$index,$index,x3
	add	$inp,$inp,$index,lsl#1
	mov	$index,#96/16
	nop
.Loop_gather_w6:
	ldrh	w4,[$inp,#64*0]
	// loop control
	subs	$index,$index,#1
	ldrh	w5,[$inp,#64*1]
	ldrh	w6,[$inp,#64*2]
	ldrh	w7,[$inp,#64*3]
	ldrh	w8,[$inp,#64*4]
	ldrh	w9,[$inp,#64*5]
	ldrh	w10,[$inp,#64*6]
	ldrh	w11,[$inp,#64*7]
	// $inp+=512
	add	$inp,$inp,#64*8
	// concat 8 16-bit into 2 64-bit 
	orr	x4,x4,x5,lsl#16
	orr	x6,x6,x7,lsl#16
	orr	x8,x8,x9,lsl#16
	orr x10,x10,x11,lsl#16

	orr	x4,x4,x6,lsl#32
	orr	x8,x8,x10,lsl#32

	// if $index=0, output=0
	and	x4,x4,x3
	and x8,x8,x3
	// store 2 64-bit value
	stp	x4,x8,[$out],#16
	b.ne	.Loop_gather_w6

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_gather_w6,.-ecp_sm2z256_gather_w6

// void	ecp_sm2z256_scatter_w7_unfixed_point(void *x0,const P256_POINT_AFFINE *x1,
//					 int x2);
.globl	ecp_sm2z256_scatter_w7_unfixed_point
.type	ecp_sm2z256_scatter_w7_unfixed_point,%function
.align	4
ecp_sm2z256_scatter_w7_unfixed_point:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0
	add	$out,$out,$index
	sub $out,$out,#1
	// each loop handle 8B, 1 point = 96B, so loop num = 12
	mov	$index,#96/8
.Loop_scatter_w7_unfixed_point:
	// load 64-bit from $inp and update $inp
	ldr	x3,[$inp],#8
	subs	$index,$index,#1
	// put the i-th Byte
	strb	w3,[$out,#64*0]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*1]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*2]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*3]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*4]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*5]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*6]
	lsr	x3,x3,#8
	strb	w3,[$out,#64*7]
	add	$out,$out,#64*8
	b.ne	.Loop_scatter_w7_unfixed_point

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_scatter_w7_unfixed_point,.-ecp_sm2z256_scatter_w7_unfixed_point

// void ecp_sm2z256_gather_w7_unfixed_point(P256_POINT_AFFINE *val,
//                            const P256_POINT_AFFINE *in_t, int idx);
.globl	ecp_sm2z256_gather_w7_unfixed_point
.type	ecp_sm2z256_gather_w7_unfixed_point,%function
.align	4
ecp_sm2z256_gather_w7_unfixed_point:
	stp	x29,x30,[sp,#-16]!
	add	x29,sp,#0

	cmp	$index,xzr
	csetm	x3,ne
	add	$index,$index,x3
	add	$inp,$inp,$index
	mov	$index,#96/8
	nop
// ldrb: load a byte with zero-extended
.Loop_gather_w7_unfixed_point:
	ldrb	w4,[$inp,#64*0]
	subs	$index,$index,#1
	ldrb	w5,[$inp,#64*1]
	ldrb	w6,[$inp,#64*2]
	ldrb	w7,[$inp,#64*3]
	ldrb	w8,[$inp,#64*4]
	ldrb	w9,[$inp,#64*5]
	ldrb	w10,[$inp,#64*6]
	ldrb	w11,[$inp,#64*7]
	// $inp+=512
	add	$inp,$inp,#64*8
	// concat 8 8-bit into 1 64-bit 
	orr	x4,x4,x5,lsl#8
	orr	x6,x6,x7,lsl#8
	orr	x8,x8,x9,lsl#8
	orr	x4,x4,x6,lsl#16
	orr	x10,x10,x11,lsl#8
	orr	x4,x4,x8,lsl#32
	orr	x4,x4,x10,lsl#48
	// if $index=0, output=0
	and	x4,x4,x3
	// store the 64-bit value
	str	x4,[$out],#8
	b.ne	.Loop_gather_w7_unfixed_point

	ldr	x29,[sp],#16
	ret
.size	ecp_sm2z256_gather_w7_unfixed_point,.-ecp_sm2z256_gather_w7_unfixed_point
___
}
else
{
my ($out,$inp,$index)=map("x$_",(0..2));
$code.=<<___;
// void	ecp_sm2z256_scatter_w5_neon(void *x0,const P256_POINT *x1,
//					 int x2);
.globl	ecp_sm2z256_scatter_w5_neon
.type	ecp_sm2z256_scatter_w5_neon,%function
.align	4
ecp_sm2z256_scatter_w5_neon:
	// 1 point = 3 * 32B = 6 vectors
	ld1 {v0.2d, v1.2d, v2.2d, v3.2d}, [$inp], 64
	// $index = ($index - 1) * 3 * 32
	sub $index, $index, 1
	add $index, $index, $index, lsl 1	// $index = $index + $index<<1
	lsl $index, $index, 5
	ld1 {v4.2d, v5.2d}, [$inp]
	add $out, $out, $index
	st1 {v0.2d, v1.2d, v2.2d, v3.2d}, [$out], 64
	st1 {v4.2d, v5.2d}, [$out]
	ret
.size	ecp_sm2z256_scatter_w5_neon,.-ecp_sm2z256_scatter_w5_neon

// void	ecp_sm2z256_gather_w5_neon(P256_POINT *x0,const void *x1,
//					      int x2);
// v0: 4; v1: index (int idx);
// v2, v3, v4: 1+4i, 2+4i, 3+4i;
// v5-v10: results;
// v11-v13: masks;
// v14-v31: points value
.globl	ecp_sm2z256_gather_w5_neon
.type	ecp_sm2z256_gather_w5_neon,%function
.align	4
ecp_sm2z256_gather_w5_neon:
	// each 64-bit items is 3
	movi	v0.4s, 3
	// index
	dup	v1.4s, w2
	// each 32-bit items is 1+3i/2+3i/3+3i
	movi	v2.4s, 1
	movi	v3.4s, 2
	movi	v4.4s, 3
	// clear v5-v10 for saving results
	eor	v5.16b, v5.16b, v5.16b
	eor	v6.16b, v6.16b, v6.16b
	eor	v7.16b, v7.16b, v7.16b
	eor	v8.16b, v8.16b, v8.16b
	eor	v9.16b, v9.16b, v9.16b
	eor	v10.16b, v10.16b, v10.16b
	// for (i = 0; i < 5; i++) each loop scan three points
	mov	x3, 5
.Loop_gather_w5_neon:
	// load 3 points, 6 vectors can accommodate 1 points
	ld1	{v14.2d, v15.2d, v16.2d, v17.2d}, [x1], 64
	ld1	{v18.2d, v19.2d, v20.2d, v21.2d}, [x1], 64
	ld1	{v22.2d, v23.2d, v24.2d, v25.2d}, [x1], 64
	ld1	{v26.2d, v27.2d, v28.2d, v29.2d}, [x1], 64
	ld1 {v30.2d, v31.2d}, [x1], 32
	// generate masks according to index
	cmeq	v11.4s, v2.4s, v1.4s
	cmeq	v12.4s, v3.4s, v1.4s
	cmeq	v13.4s, v4.4s, v1.4s
	// add 3 for each items of v2-v4
	add	v2.4s, v2.4s, v0.4s
	add	v3.4s, v3.4s, v0.4s
	add	v4.4s, v4.4s, v0.4s
	// point AND with masks for getting the point we want
	and	v14.16b, v14.16b, v11.16b
	and	v15.16b, v15.16b, v11.16b
	and	v16.16b, v16.16b, v11.16b
	and	v17.16b, v17.16b, v11.16b
	and	v18.16b, v18.16b, v11.16b
	and	v19.16b, v19.16b, v11.16b

	and	v20.16b, v20.16b, v12.16b
	and	v21.16b, v21.16b, v12.16b
	and	v22.16b, v22.16b, v12.16b
	and	v23.16b, v23.16b, v12.16b
	and	v24.16b, v24.16b, v12.16b
	and	v25.16b, v25.16b, v12.16b

	and	v26.16b, v26.16b, v13.16b
	and	v27.16b, v27.16b, v13.16b
	and	v28.16b, v28.16b, v13.16b
	and	v29.16b, v29.16b, v13.16b
	and	v30.16b, v30.16b, v13.16b
	and	v31.16b, v31.16b, v13.16b

	// masked_point XOR with results for getting final results
	eor	v5.16b, v5.16b, v14.16b
	eor	v6.16b, v6.16b, v15.16b
	eor	v7.16b, v7.16b, v16.16b
	eor	v8.16b, v8.16b, v17.16b
	eor	v9.16b, v9.16b, v18.16b
	eor	v10.16b, v10.16b, v19.16b

	eor	v5.16b, v5.16b, v20.16b
	eor	v6.16b, v6.16b, v21.16b
	eor	v7.16b, v7.16b, v22.16b
	eor	v8.16b, v8.16b, v23.16b
	eor	v9.16b, v9.16b, v24.16b
	eor	v10.16b, v10.16b, v25.16b

	eor	v5.16b, v5.16b, v26.16b
	eor	v6.16b, v6.16b, v27.16b
	eor	v7.16b, v7.16b, v28.16b
	eor	v8.16b, v8.16b, v29.16b
	eor	v9.16b, v9.16b, v30.16b
	eor	v10.16b, v10.16b, v31.16b

	subs	x3, x3, 1
	b.ne	.Loop_gather_w5_neon

	// 16-th point
	ld1	{v14.2d, v15.2d, v16.2d, v17.2d}, [x1], 64
	ld1 {v18.2d, v19.2d}, [x1], 32
	// generate masks according to index
	cmeq	v11.4s, v2.4s, v1.4s
	// point AND with masks for getting the point we want
	and	v14.16b, v14.16b, v11.16b
	and	v15.16b, v15.16b, v11.16b
	and	v16.16b, v16.16b, v11.16b
	and	v17.16b, v17.16b, v11.16b
	and	v18.16b, v18.16b, v11.16b
	and	v19.16b, v19.16b, v11.16b
	eor	v5.16b, v5.16b, v14.16b
	eor	v6.16b, v6.16b, v15.16b
	eor	v7.16b, v7.16b, v16.16b
	eor	v8.16b, v8.16b, v17.16b
	eor	v9.16b, v9.16b, v18.16b
	eor	v10.16b, v10.16b, v19.16b

	st1	{v5.2d, v6.2d, v7.2d, v8.2d}, [x0], 64
	st1 {v9.2d, v10.2d}, [x0]
	ret
.size	ecp_sm2z256_gather_w5_neon,.-ecp_sm2z256_gather_w5_neon

// void	ecp_sm2z256_scatter_w7_neon(void *x0,const P256_POINT_AFFINE *x1,
//					 int x2);
.globl	ecp_sm2z256_scatter_w7_neon
.type	ecp_sm2z256_scatter_w7_neon,%function
.align	4
ecp_sm2z256_scatter_w7_neon:
	// a point is 64B, a vector is 16B, so a point == 4 vectors
	// load a point
	ld1 {v0.2d, v1.2d, v2.2d, v3.2d}, [$inp]
	// $out+=$index*(2^64)
	add $out, $out, $index, lsl 6
	// store a point
	st1 {v0.2d, v1.2d, v2.2d, v3.2d}, [$out]
	ret
.size	ecp_sm2z256_scatter_w7_neon,.-ecp_sm2z256_scatter_w7_neon

// void ecp_sm2z256_gather_w7_neon(P256_POINT_AFFINE *val,
//                            const P256_POINT_AFFINE *in_t, int idx);
// v0: 4; v1: index (int idx);
// v2, v3, v4, v5: 1+4i, 2+4i, 3+4i, 4+4i;
// v6, v7, v8, v9: results;
// v10,v11,v12,v13: masks;
// v14-v29: points value
.globl	ecp_sm2z256_gather_w7_neon
.type	ecp_sm2z256_gather_w7_neon,%function
.align	4
ecp_sm2z256_gather_w7_neon:
	// each 64-bit items is 4
	movi v0.4s, 4
	// index
	dup v1.4s, w2
	// each 32-bit items is 1+4i/2+4i/3+4i/4+4i
	movi v2.4s, 1
	movi v3.4s, 2
	movi v4.4s, 3
	movi v5.4s, 4
	// clear v6-v9 for saving results
	eor v6.16b, v6.16b, v6.16b
	eor v7.16b, v7.16b, v7.16b
	eor v8.16b, v8.16b, v8.16b
	eor v9.16b, v9.16b, v9.16b
	// for (i = 0; i < 16; i++) each loop scan four points
	mov x3, 16
.Loop_gather_w7_neon:
	// load 4 points, 4 vectors can accommodate 1 points
	ld1 {v14.2d, v15.2d, v16.2d, v17.2d}, [$inp], 64	// (4i)  -th point
	ld1 {v18.2d, v19.2d, v20.2d, v21.2d}, [$inp], 64	// (4i+1)-th point
	ld1 {v22.2d, v23.2d, v24.2d, v25.2d}, [$inp], 64	// (4i+2)-th point
	ld1 {v26.2d, v27.2d, v28.2d, v29.2d}, [$inp], 64	// (4i+3)-th point
	// generate masks according to index
	cmeq v10.4s, v2.4s, v1.4s
	cmeq v11.4s, v3.4s, v1.4s
	cmeq v12.4s, v4.4s, v1.4s
	cmeq v13.4s, v5.4s, v1.4s
	// add 4 for each items of v2-v5
	add v2.4s, v2.4s, v0.4s
	add v3.4s, v3.4s, v0.4s
	add v4.4s, v4.4s, v0.4s
	add v5.4s, v5.4s, v0.4s
	// point AND with masks for getting the point we want
	and v14.16b, v14.16b, v10.16b
	and v15.16b, v15.16b, v10.16b
	and v16.16b, v16.16b, v10.16b
	and v17.16b, v17.16b, v10.16b

	and v18.16b, v18.16b, v11.16b
	and v19.16b, v19.16b, v11.16b
	and v20.16b, v20.16b, v11.16b
	and v21.16b, v21.16b, v11.16b

	and v22.16b, v22.16b, v12.16b
	and v23.16b, v23.16b, v12.16b
	and v24.16b, v24.16b, v12.16b
	and v25.16b, v25.16b, v12.16b

	and v26.16b, v26.16b, v13.16b
	and v27.16b, v27.16b, v13.16b
	and v28.16b, v28.16b, v13.16b
	and v29.16b, v29.16b, v13.16b

	// masked_point XOR with results for getting final results
	eor v6.16b, v6.16b, v14.16b
	eor v7.16b, v7.16b, v15.16b
	eor v8.16b, v8.16b, v16.16b
	eor v9.16b, v9.16b, v17.16b

	eor v6.16b, v6.16b, v18.16b
	eor v7.16b, v7.16b, v19.16b
	eor v8.16b, v8.16b, v20.16b
	eor v9.16b, v9.16b, v21.16b

	eor v6.16b, v6.16b, v22.16b
	eor v7.16b, v7.16b, v23.16b
	eor v8.16b, v8.16b, v24.16b
	eor v9.16b, v9.16b, v25.16b

	eor v6.16b, v6.16b, v26.16b
	eor v7.16b, v7.16b, v27.16b
	eor v8.16b, v8.16b, v28.16b
	eor v9.16b, v9.16b, v29.16b

	subs x3, x3, 1
	b.ne .Loop_gather_w7_neon

	st1 {v6.2d, v7.2d, v8.2d, v9.2d}, [$out]
	ret
.size	ecp_sm2z256_gather_w7_neon,.-ecp_sm2z256_gather_w7_neon
___
}

foreach (split("\n",$code)) {
	s/\`([^\`]*)\`/eval $1/ge;

	print $_,"\n";
}
close STDOUT or die "error closing STDOUT: $!";	# enforce flush

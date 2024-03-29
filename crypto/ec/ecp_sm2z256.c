#include "internal/deprecated.h"

#include <string.h>

#include "internal/cryptlib.h"
#include "crypto/bn.h"
#include "ec_local.h"
#include "internal/refcount.h"

#if BN_BITS2 != 64
# define TOBN(hi,lo)    lo,hi
#else
# define TOBN(hi,lo)    ((BN_ULONG)hi<<32|lo)
#endif

#if defined(__GNUC__)
# define ALIGN32        __attribute((aligned(32)))
#elif defined(_MSC_VER)
# define ALIGN32        __declspec(align(32))
#else
# define ALIGN32
#endif

#define ALIGNPTR(p,N)   ((unsigned char *)p+N-(size_t)p%N)
#define P256_LIMBS      (256/BN_BITS2)

typedef unsigned short u16;

typedef struct {
    BN_ULONG X[P256_LIMBS];
    BN_ULONG Y[P256_LIMBS];
    BN_ULONG Z[P256_LIMBS];
} P256_POINT;

typedef struct {
    BN_ULONG X[P256_LIMBS];
    BN_ULONG Y[P256_LIMBS];
} P256_POINT_AFFINE;

typedef P256_POINT_AFFINE PRECOMP256_ROW[64];

/* structure for precomputed multiples of the generator */
struct sm2z256_pre_comp_st {
    const EC_GROUP *group;      /* Parent EC_GROUP object */
    size_t w;                   /* Window size */
    /*
     * Constant time access to the X and Y coordinates of the pre-computed,
     * generator multiplies, in the Montgomery domain. Pre-calculated
     * multiplies are stored in affine form.
     */
    PRECOMP256_ROW *precomp;
    void *precomp_storage;
    CRYPTO_REF_COUNT references;
    CRYPTO_RWLOCK *lock;
};

/* Functions implemented in assembly */
/*
 * Most of below mentioned functions *preserve* the property of inputs
 * being fully reduced, i.e. being in [0, modulus) range. Simply put if
 * inputs are fully reduced, then output is too. Note that reverse is
 * not true, in sense that given partially reduced inputs output can be
 * either, not unlikely reduced. And "most" in first sentence refers to
 * the fact that given the calculations flow one can tolerate that
 * addition, 1st function below, produces partially reduced result *if*
 * multiplications by 2 and 3, which customarily use addition, fully
 * reduce it. This effectively gives two options: a) addition produces
 * fully reduced result [as long as inputs are, just like remaining
 * functions]; b) addition is allowed to produce partially reduced
 * result, but multiplications by 2 and 3 perform additional reduction
 * step. Choice between the two can be platform-specific, but it was a)
 * in all cases so far...
 */
/* Modular add: res = a+b mod P   */
void ecp_sm2z256_add(BN_ULONG res[P256_LIMBS],
                      const BN_ULONG a[P256_LIMBS],
                      const BN_ULONG b[P256_LIMBS]);
/* Modular mul by 2: res = 2*a mod P */
void ecp_sm2z256_mul_by_2(BN_ULONG res[P256_LIMBS],
                           const BN_ULONG a[P256_LIMBS]);
/* Modular mul by 3: res = 3*a mod P */
void ecp_sm2z256_mul_by_3(BN_ULONG res[P256_LIMBS],
                           const BN_ULONG a[P256_LIMBS]);

/* Modular div by 2: res = a/2 mod P */
void ecp_sm2z256_div_by_2(BN_ULONG res[P256_LIMBS],
                           const BN_ULONG a[P256_LIMBS]);
/* Modular sub: res = a-b mod P   */
void ecp_sm2z256_sub(BN_ULONG res[P256_LIMBS],
                      const BN_ULONG a[P256_LIMBS],
                      const BN_ULONG b[P256_LIMBS]);
/* Modular neg: res = -a mod P    */
void ecp_sm2z256_neg(BN_ULONG res[P256_LIMBS], const BN_ULONG a[P256_LIMBS]);
/* Montgomery mul: res = a*b*2^-256 mod P */
void ecp_sm2z256_mul_mont(BN_ULONG res[P256_LIMBS],
                           const BN_ULONG a[P256_LIMBS],
                           const BN_ULONG b[P256_LIMBS]);
/* Montgomery sqr: res = a*a*2^-256 mod P */
void ecp_sm2z256_sqr_mont(BN_ULONG res[P256_LIMBS],
                           const BN_ULONG a[P256_LIMBS]);
/* Convert a number from Montgomery domain, by multiplying with 1 */
void ecp_sm2z256_from_mont(BN_ULONG res[P256_LIMBS],
                            const BN_ULONG in[P256_LIMBS]);
/* Convert a number to Montgomery domain, by multiplying with 2^512 mod P*/
void ecp_sm2z256_to_mont(BN_ULONG res[P256_LIMBS],
                          const BN_ULONG in[P256_LIMBS]);
/* Functions that perform constant time access to the precomputed tables */
void ecp_sm2z256_scatter_w5(P256_POINT *val,
                             const P256_POINT *in_t, int idx);
void ecp_sm2z256_gather_w5(P256_POINT *val,
                            const P256_POINT *in_t, int idx);
void ecp_sm2z256_scatter_w7(P256_POINT_AFFINE *val,
                             const P256_POINT_AFFINE *in_t, int idx);
void ecp_sm2z256_gather_w7(P256_POINT_AFFINE *val,
                            const P256_POINT_AFFINE *in_t, int idx);
void ecp_sm2z256_scatter_w7_unfixed_point(void *x0,
                            const P256_POINT_AFFINE *x1, int x2);
void ecp_sm2z256_gather_w7_unfixed_point(P256_POINT_AFFINE *val,
                            const P256_POINT_AFFINE *in_t, int idx);
// void ecp_sm2z256_scatter_w5_neon(P256_POINT *val,
//                              const P256_POINT *in_t, int idx);
// void ecp_sm2z256_gather_w5_neon(P256_POINT *val,
//                             const P256_POINT *in_t, int idx);      
// void ecp_sm2z256_scatter_w7_neon(P256_POINT_AFFINE *val,
//                              const P256_POINT_AFFINE *in_t, int idx);
// void ecp_sm2z256_gather_w7_neon(P256_POINT_AFFINE *val,
//                             const P256_POINT_AFFINE *in_t, int idx);
// #define ecp_sm2z256_scatter_w7 ecp_sm2z256_scatter_w7_neon
// #define ecp_sm2z256_gather_w7 ecp_sm2z256_gather_w7_neon

// #define ecp_sm2z256_scatter_w5 ecp_sm2z256_scatter_w5_neon
// #define ecp_sm2z256_gather_w5 ecp_sm2z256_gather_w5_neon
/* One converted into the Montgomery domain */
static const BN_ULONG ONE[P256_LIMBS] = {
    TOBN(0x00000000, 0x00000001), TOBN(0x00000000, 0xffffffff),
    TOBN(0x00000000, 0x00000000), TOBN(0x00000001, 0x00000000)
};

static SM2Z256_PRE_COMP *ecp_sm2z256_pre_comp_new(const EC_GROUP *group);

/* Precomputed tables for the default generator */
extern const PRECOMP256_ROW ecp_sm2z256_precomputed[37];

/* Recode window to a signed digit, see ecp_nistputil.c for details */
static unsigned int _booth_recode_w4(unsigned int in)
{
    unsigned int s, d;

    s = ~((in >> 4) - 1);
    d = (1 << 5) - in - 1;
    d = (d & s) | (in & ~s);
    d = (d >> 1) + (d & 1);

    return (d << 1) + (s & 1);
}

static unsigned int _booth_recode_w5(unsigned int in)
{
    unsigned int s, d;

    s = ~((in >> 5) - 1);
    d = (1 << 6) - in - 1;
    d = (d & s) | (in & ~s);
    d = (d >> 1) + (d & 1);

    return (d << 1) + (s & 1);
}

static unsigned int _booth_recode_w6(unsigned int in)
{
    unsigned int s, d;

    s = ~((in >> 6) - 1);
    d = (1 << 7) - in - 1;
    d = (d & s) | (in & ~s);
    d = (d >> 1) + (d & 1);

    return (d << 1) + (s & 1);
}

/* 
 * the LSB of the returned value is sign bit, remaining is absoluate value
 * give two examples for understanding this function
 * e1: value = 0x78 = 120, in = value<<1 = 0xf0 return: sign = 1, value = 8 i.e. -8
 * e2: value = 0x7, in = value<<1 = 0x0e return: sign = 0, value = 0x7 i.e. +7
 * 
 * How to understand this function from the perspective of the encoding of scalar?
 * Suppose the 14-bit scalar is: 
 * s_13 s_12 s_11 s_10 s_9 s_8 s_7 | s_6 s_5 s_4 s_3 s_2 s_1 s_0 = 
 * 0    0    0    0    1   1   1   | 1   1   1   1   0   0   0   =
 * 0x07                            | 0x78                        =
 * 7*(2^7)         +               | 120                         = 1016
 * 1-th call: in = (s_6 s_5 ... s_0 0) = 0x78<<1, return: value = 8, sign = 1, i.e. -8
 * 2-th call: in = (s_12 s_11 ... s_6) = 0x0f, return: value = 0x8, sign = 0, i.e. +8
 * 3-th call: in = (0 0 ...0 s_13) = 0x0, return: value = 0, sign = 0, i.e. +0 
 * now the scalar is:
 * 8*(2^7) - 8 = 1016
 * 
 * if we use the original encoding method, we have to pre-compute 128 points;
 * if we use the booth encoding method, we can only pre-compute 64 points.
 */
static unsigned int _booth_recode_w7(unsigned int in)
{
    unsigned int s, d;
    // if in's sign = 0 then s = 0...0
    // if in's sign = 1 then s = 1...1
    s = ~((in >> 7) - 1);
    // bitwise negation with 7-bit width
    d = (1 << 8) - in - 1;
    // if in's sign = 0, d = in
    // if in's sign = 1, d = d
    d = (d & s) | (in & ~s);
    // d & 1 is the sign bit of previous word
    d = (d >> 1) + (d & 1);
    return (d << 1) + (s & 1);
}

static void copy_conditional(BN_ULONG dst[P256_LIMBS],
                             const BN_ULONG src[P256_LIMBS], BN_ULONG move)
{
    BN_ULONG mask1 = 0-move;
    BN_ULONG mask2 = ~mask1;

    dst[0] = (src[0] & mask1) ^ (dst[0] & mask2);
    dst[1] = (src[1] & mask1) ^ (dst[1] & mask2);
    dst[2] = (src[2] & mask1) ^ (dst[2] & mask2);
    dst[3] = (src[3] & mask1) ^ (dst[3] & mask2);
    if (P256_LIMBS == 8) {
        dst[4] = (src[4] & mask1) ^ (dst[4] & mask2);
        dst[5] = (src[5] & mask1) ^ (dst[5] & mask2);
        dst[6] = (src[6] & mask1) ^ (dst[6] & mask2);
        dst[7] = (src[7] & mask1) ^ (dst[7] & mask2);
    }
}

static BN_ULONG is_zero(BN_ULONG in)
{
    in |= (0 - in);
    in = ~in;
    in >>= BN_BITS2 - 1;
    return in;
}

static BN_ULONG is_equal(const BN_ULONG a[P256_LIMBS],
                         const BN_ULONG b[P256_LIMBS])
{
    BN_ULONG res;

    res = a[0] ^ b[0];
    res |= a[1] ^ b[1];
    res |= a[2] ^ b[2];
    res |= a[3] ^ b[3];
    if (P256_LIMBS == 8) {
        res |= a[4] ^ b[4];
        res |= a[5] ^ b[5];
        res |= a[6] ^ b[6];
        res |= a[7] ^ b[7];
    }

    return is_zero(res);
}

static BN_ULONG is_one(const BIGNUM *z)
{
    BN_ULONG res = 0;
    BN_ULONG *a = bn_get_words(z);

    if (bn_get_top(z) == (P256_LIMBS - P256_LIMBS / 8)) {
        res = a[0] ^ ONE[0];
        res |= a[1] ^ ONE[1];
        res |= a[2] ^ ONE[2];
        res |= a[3] ^ ONE[3];
        if (P256_LIMBS == 8) {
            res |= a[4] ^ ONE[4];
            res |= a[5] ^ ONE[5];
            res |= a[6] ^ ONE[6];
            /*
             * no check for a[7] (being zero) on 32-bit platforms,
             * because value of "one" takes only 7 limbs.
             */
        }
        res = is_zero(res);
    }

    return res;
}

/*
 * For reference, this macro is used only when new ecp_sm2z256 assembly
 * module is being developed.  For example, configure with
 * -DECP_SM2Z256_REFERENCE_IMPLEMENTATION and implement only functions
 * performing simplest arithmetic operations on 256-bit vectors. Then
 * work on implementation of higher-level functions performing point
 * operations. Then remove ECP_SM2Z256_REFERENCE_IMPLEMENTATION
 * and never define it again. (The correct macro denoting presence of
 * ecp_sm2z256 module is ECP_SM2Z256_ASM.)
 */
#ifndef ECP_SM2Z256_REFERENCE_IMPLEMENTATION
void ecp_sm2z256_point_double(P256_POINT *r, const P256_POINT *a);
void ecp_sm2z256_point_add(P256_POINT *r,
                            const P256_POINT *a, const P256_POINT *b);
void ecp_sm2z256_point_add_affine(P256_POINT *r,
                                   const P256_POINT *a,
                                   const P256_POINT_AFFINE *b);
#else
/* Point double: r = 2*a */
static void ecp_sm2z256_point_double(P256_POINT *r, const P256_POINT *a)
{
    BN_ULONG S[P256_LIMBS];
    BN_ULONG M[P256_LIMBS];
    BN_ULONG Zsqr[P256_LIMBS];
    BN_ULONG tmp0[P256_LIMBS];

    const BN_ULONG *in_x = a->X;
    const BN_ULONG *in_y = a->Y;
    const BN_ULONG *in_z = a->Z;

    BN_ULONG *res_x = r->X;
    BN_ULONG *res_y = r->Y;
    BN_ULONG *res_z = r->Z;
    // S=2Y
    ecp_sm2z256_mul_by_2(S, in_y);
    // Zsqr=Z^2
    ecp_sm2z256_sqr_mont(Zsqr, in_z);
    // S=4Y^2
    ecp_sm2z256_sqr_mont(S, S);
    // resZ=2*Y*Z
    ecp_sm2z256_mul_mont(res_z, in_z, in_y);
    ecp_sm2z256_mul_by_2(res_z, res_z);
    // M=X+Z^2
    ecp_sm2z256_add(M, in_x, Zsqr);
    // Zsqr=X-Z^2
    ecp_sm2z256_sub(Zsqr, in_x, Zsqr);
    // resY=S^2
    ecp_sm2z256_sqr_mont(res_y, S);
    // resY=S^2/2=8Y^4
    ecp_sm2z256_div_by_2(res_y, res_y);
    // M=(X+Z^2)*(X-Z^2)=X^2-Z^4
    ecp_sm2z256_mul_mont(M, M, Zsqr);
    // M=3*(X^2-Z^4)
    ecp_sm2z256_mul_by_3(M, M);
    // S=4XY^2
    ecp_sm2z256_mul_mont(S, S, in_x);
    // tmp0=8XY^2
    ecp_sm2z256_mul_by_2(tmp0, S);
    // resX=M^2=(3*(X+Z^2)*(X-Z^2))^2=9*(X^2-Z^4)^2
    ecp_sm2z256_sqr_mont(res_x, M);
    // resX=9*(X^2-Z^4)^2-2S
    ecp_sm2z256_sub(res_x, res_x, tmp0);
    // S=S-resX
    ecp_sm2z256_sub(S, S, res_x);
    // S=S*M
    ecp_sm2z256_mul_mont(S, S, M);
    // resY=S-8Y^4
    ecp_sm2z256_sub(res_y, S, res_y);
}

/* Point addition: r = a+b */
static void ecp_sm2z256_point_add(P256_POINT *r,
                                   const P256_POINT *a, const P256_POINT *b)
{
    BN_ULONG U2[P256_LIMBS], S2[P256_LIMBS];
    BN_ULONG U1[P256_LIMBS], S1[P256_LIMBS];
    BN_ULONG Z1sqr[P256_LIMBS];
    BN_ULONG Z2sqr[P256_LIMBS];
    BN_ULONG H[P256_LIMBS], R[P256_LIMBS];
    BN_ULONG Hsqr[P256_LIMBS];
    BN_ULONG Rsqr[P256_LIMBS];
    BN_ULONG Hcub[P256_LIMBS];

    BN_ULONG res_x[P256_LIMBS];
    BN_ULONG res_y[P256_LIMBS];
    BN_ULONG res_z[P256_LIMBS];

    BN_ULONG in1infty, in2infty;

    const BN_ULONG *in1_x = a->X;
    const BN_ULONG *in1_y = a->Y;
    const BN_ULONG *in1_z = a->Z;

    const BN_ULONG *in2_x = b->X;
    const BN_ULONG *in2_y = b->Y;
    const BN_ULONG *in2_z = b->Z;

    /*
     * Infinity in encoded as (,,0)
     */
    in1infty = (in1_z[0] | in1_z[1] | in1_z[2] | in1_z[3]);
    if (P256_LIMBS == 8)
        in1infty |= (in1_z[4] | in1_z[5] | in1_z[6] | in1_z[7]);

    in2infty = (in2_z[0] | in2_z[1] | in2_z[2] | in2_z[3]);
    if (P256_LIMBS == 8)
        in2infty |= (in2_z[4] | in2_z[5] | in2_z[6] | in2_z[7]);

    in1infty = is_zero(in1infty);
    in2infty = is_zero(in2infty);

    ecp_sm2z256_sqr_mont(Z2sqr, in2_z);        /* Z2^2 */
    ecp_sm2z256_sqr_mont(Z1sqr, in1_z);        /* Z1^2 */

    ecp_sm2z256_mul_mont(S1, Z2sqr, in2_z);    /* S1 = Z2^3 */
    ecp_sm2z256_mul_mont(S2, Z1sqr, in1_z);    /* S2 = Z1^3 */

    ecp_sm2z256_mul_mont(S1, S1, in1_y);       /* S1 = Y1*Z2^3 */
    ecp_sm2z256_mul_mont(S2, S2, in2_y);       /* S2 = Y2*Z1^3 */
    ecp_sm2z256_sub(R, S2, S1);                /* R = S2 - S1 */

    ecp_sm2z256_mul_mont(U1, in1_x, Z2sqr);    /* U1 = X1*Z2^2 */
    ecp_sm2z256_mul_mont(U2, in2_x, Z1sqr);    /* U2 = X2*Z1^2 */
    ecp_sm2z256_sub(H, U2, U1);                /* H = U2 - U1 */

    /*
     * The formulae are incorrect if the points are equal so we check for
     * this and do doubling if this happens.
     *
     * Points here are in Jacobian projective coordinates (Xi, Yi, Zi)
     * that are bound to the affine coordinates (xi, yi) by the following
     * equations:
     *     - xi = Xi / (Zi)^2
     *     - y1 = Yi / (Zi)^3
     *
     * For the sake of optimization, the algorithm operates over
     * intermediate variables U1, U2 and S1, S2 that are derived from
     * the projective coordinates:
     *     - U1 = X1 * (Z2)^2 ; U2 = X2 * (Z1)^2
     *     - S1 = Y1 * (Z2)^3 ; S2 = Y2 * (Z1)^3
     *
     * It is easy to prove that is_equal(U1, U2) implies that the affine
     * x-coordinates are equal, or either point is at infinity.
     * Likewise is_equal(S1, S2) implies that the affine y-coordinates are
     * equal, or either point is at infinity.
     *
     * The special case of either point being the point at infinity (Z1 or Z2
     * is zero), is handled separately later on in this function, so we avoid
     * jumping to point_double here in those special cases.
     *
     * When both points are inverse of each other, we know that the affine
     * x-coordinates are equal, and the y-coordinates have different sign.
     * Therefore since U1 = U2, we know H = 0, and therefore Z3 = H*Z1*Z2
     * will equal 0, thus the result is infinity, if we simply let this
     * function continue normally.
     *
     * We use bitwise operations to avoid potential side-channels introduced by
     * the short-circuiting behaviour of boolean operators.
     */
    if (is_equal(U1, U2) & ~in1infty & ~in2infty & is_equal(S1, S2)) {
        /*
         * This is obviously not constant-time but it should never happen during
         * single point multiplication, so there is no timing leak for ECDH or
         * ECDSA signing.
         */
        ecp_sm2z256_point_double(r, a);
        return;
    }

    ecp_sm2z256_sqr_mont(Rsqr, R);             /* R^2 */
    ecp_sm2z256_mul_mont(res_z, H, in1_z);     /* Z3 = H*Z2 */
    ecp_sm2z256_sqr_mont(Hsqr, H);             /* H^2 */
    ecp_sm2z256_mul_mont(res_z, res_z, in2_z); /* Z3 = H*Z1*Z2 */
    ecp_sm2z256_mul_mont(Hcub, Hsqr, H);       /* H^3 */

    ecp_sm2z256_mul_mont(U2, U1, Hsqr);        /* U2 = U1*H^2 */
    ecp_sm2z256_mul_by_2(Hsqr, U2);            /* Hsqr = 2*U1*H^2 */

    ecp_sm2z256_sub(res_x, Rsqr, Hsqr);        /* X3 = R^2-2*U1*H^2 */
    ecp_sm2z256_sub(res_x, res_x, Hcub);       /* X3 = R^2-2*U1*H^2-H^3=R^2-(U1+U2)*H^2 */

    ecp_sm2z256_sub(res_y, U2, res_x);         /* Y3 = U1*H^2-X3 */

    ecp_sm2z256_mul_mont(S2, S1, Hcub);        /* S2 = S1*P^3 */
    ecp_sm2z256_mul_mont(res_y, R, res_y);     /* Y3 = R*Y3 */
    ecp_sm2z256_sub(res_y, res_y, S2);         /* Y3 = R*(U1*P^2-X3)-S1*P^3 */

    copy_conditional(res_x, in2_x, in1infty);
    copy_conditional(res_y, in2_y, in1infty);
    copy_conditional(res_z, in2_z, in1infty);

    copy_conditional(res_x, in1_x, in2infty);
    copy_conditional(res_y, in1_y, in2infty);
    copy_conditional(res_z, in1_z, in2infty);

    memcpy(r->X, res_x, sizeof(res_x));
    memcpy(r->Y, res_y, sizeof(res_y));
    memcpy(r->Z, res_z, sizeof(res_z));
}

/* Point addition when b is known to be affine: r = a+b */
static void ecp_sm2z256_point_add_affine(P256_POINT *r,
                                          const P256_POINT *a,
                                          const P256_POINT_AFFINE *b)
{
    BN_ULONG U2[P256_LIMBS], S2[P256_LIMBS];
    BN_ULONG Z1sqr[P256_LIMBS];
    BN_ULONG H[P256_LIMBS], R[P256_LIMBS];
    BN_ULONG Hsqr[P256_LIMBS];
    BN_ULONG Rsqr[P256_LIMBS];
    BN_ULONG Hcub[P256_LIMBS];

    BN_ULONG res_x[P256_LIMBS];
    BN_ULONG res_y[P256_LIMBS];
    BN_ULONG res_z[P256_LIMBS];

    BN_ULONG in1infty, in2infty;

    const BN_ULONG *in1_x = a->X;
    const BN_ULONG *in1_y = a->Y;
    const BN_ULONG *in1_z = a->Z;

    const BN_ULONG *in2_x = b->X;
    const BN_ULONG *in2_y = b->Y;

    /*
     * Infinity in encoded as (,,0)
     */
    in1infty = (in1_z[0] | in1_z[1] | in1_z[2] | in1_z[3]);
    if (P256_LIMBS == 8)
        in1infty |= (in1_z[4] | in1_z[5] | in1_z[6] | in1_z[7]);

    /*
     * In affine representation we encode infinity as (0,0), which is
     * not on the curve, so it is OK
     */
    in2infty = (in2_x[0] | in2_x[1] | in2_x[2] | in2_x[3] |
                in2_y[0] | in2_y[1] | in2_y[2] | in2_y[3]);
    if (P256_LIMBS == 8)
        in2infty |= (in2_x[4] | in2_x[5] | in2_x[6] | in2_x[7] |
                     in2_y[4] | in2_y[5] | in2_y[6] | in2_y[7]);

    in1infty = is_zero(in1infty);
    in2infty = is_zero(in2infty);

    ecp_sm2z256_sqr_mont(Z1sqr, in1_z);        /* Z1^2 */

    ecp_sm2z256_mul_mont(U2, in2_x, Z1sqr);    /* U2 = X2*Z1^2 */
    ecp_sm2z256_sub(H, U2, in1_x);             /* H = U2 - U1 */

    ecp_sm2z256_mul_mont(S2, Z1sqr, in1_z);    /* S2 = Z1^3 */

    ecp_sm2z256_mul_mont(res_z, H, in1_z);     /* Z3 = H*Z1*Z2 */

    ecp_sm2z256_mul_mont(S2, S2, in2_y);       /* S2 = Y2*Z1^3 */
    ecp_sm2z256_sub(R, S2, in1_y);             /* R = S2 - S1 */

    ecp_sm2z256_sqr_mont(Hsqr, H);             /* H^2 */
    ecp_sm2z256_sqr_mont(Rsqr, R);             /* R^2 */
    ecp_sm2z256_mul_mont(Hcub, Hsqr, H);       /* H^3 */

    ecp_sm2z256_mul_mont(U2, in1_x, Hsqr);     /* U1*H^2 */
    ecp_sm2z256_mul_by_2(Hsqr, U2);            /* 2*U1*H^2 */

    ecp_sm2z256_sub(res_x, Rsqr, Hsqr);
    ecp_sm2z256_sub(res_x, res_x, Hcub);
    ecp_sm2z256_sub(H, U2, res_x);

    ecp_sm2z256_mul_mont(S2, in1_y, Hcub);
    ecp_sm2z256_mul_mont(H, H, R);
    ecp_sm2z256_sub(res_y, H, S2);

    copy_conditional(res_x, in2_x, in1infty);
    copy_conditional(res_x, in1_x, in2infty);

    copy_conditional(res_y, in2_y, in1infty);
    copy_conditional(res_y, in1_y, in2infty);

    copy_conditional(res_z, ONE, in1infty);
    copy_conditional(res_z, in1_z, in2infty);

    memcpy(r->X, res_x, sizeof(res_x));
    memcpy(r->Y, res_y, sizeof(res_y));
    memcpy(r->Z, res_z, sizeof(res_z));
}
#endif

#if (0)
/* r = in^-1 mod p */
static void ecp_sm2z256_mod_inverse(BN_ULONG r[P256_LIMBS],
                                     const BN_ULONG in[P256_LIMBS])
{
    BN_ULONG a1[P256_LIMBS];
    BN_ULONG a2[P256_LIMBS];
    BN_ULONG a3[P256_LIMBS];
    BN_ULONG a4[P256_LIMBS];
    BN_ULONG a5[P256_LIMBS];
    int i;

    ecp_sm2z256_sqr_mont(a1, in);
    ecp_sm2z256_mul_mont(a2, a1, in);
    ecp_sm2z256_sqr_mont(a3, a2);
    ecp_sm2z256_sqr_mont(a3, a3);
    ecp_sm2z256_mul_mont(a3, a3, a2);
    ecp_sm2z256_sqr_mont(a4, a3);
    ecp_sm2z256_sqr_mont(a4, a4);
    ecp_sm2z256_sqr_mont(a4, a4);
    ecp_sm2z256_sqr_mont(a4, a4);
    ecp_sm2z256_mul_mont(a4, a4, a3);
    ecp_sm2z256_sqr_mont(a5, a4);
    for (i = 0; i < 7; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a5, a5, a4);
    for (i = 0; i < 8; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a5, a5, a4);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_mul_mont(a5, a5, a3);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_mul_mont(a5, a5, a2);
    ecp_sm2z256_sqr_mont(a5, a5);
    ecp_sm2z256_mul_mont(a5, a5, in);
    ecp_sm2z256_sqr_mont(a4, a5);
    ecp_sm2z256_mul_mont(a3, a4, a1);
    ecp_sm2z256_sqr_mont(a5, a4);
    for (i = 0; i < 30; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a4, a5, a4);
    ecp_sm2z256_sqr_mont(a4, a4);
    ecp_sm2z256_mul_mont(a4, a4, in);
    ecp_sm2z256_mul_mont(a3, a4, a2);
    for (i = 0; i < 33; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a2, a5, a3);
    ecp_sm2z256_mul_mont(a3, a2, a3);
    for (i = 0; i < 32; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a2, a5, a3);
    ecp_sm2z256_mul_mont(a3, a2, a3);
    ecp_sm2z256_mul_mont(a4, a2, a4);
    for (i = 0; i < 32; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a2, a5, a3);
    ecp_sm2z256_mul_mont(a3, a2, a3);
    ecp_sm2z256_mul_mont(a4, a2, a4);
    for (i = 0; i < 32; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a2, a5, a3);
    ecp_sm2z256_mul_mont(a3, a2, a3);
    ecp_sm2z256_mul_mont(a4, a2, a4);
    for (i = 0; i < 32; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(a2, a5, a3);
    ecp_sm2z256_mul_mont(a3, a2, a3);
    ecp_sm2z256_mul_mont(a4, a2, a4);
    for (i = 0; i < 32; i++) {
        ecp_sm2z256_sqr_mont(a5, a5);
    }
    ecp_sm2z256_mul_mont(r, a4, a5);
}
#endif

/* r = in^-2 = in^(q-3) mod p
 * See: https://briansmith.org/ecc-inversion-addition-chains-01#p256_scalar_inversion
 */
void ecp_sm2z256_mod_inverse_sqr(BN_ULONG r[P256_LIMBS],
                                       const BN_ULONG in[P256_LIMBS])
{
    BN_ULONG xtp[P256_LIMBS];
    BN_ULONG x30[P256_LIMBS];
    // BN_ULONG x31[P256_LIMBS];
    BN_ULONG x32[P256_LIMBS];
    // don't change them
    #define x1 in
    #define x2 x30
    #define x4 x32
    #define x6 xtp
    #define x12 x30
    #define x24 x32
    #define x31 r
    int i;
    // construct x30, 31, x32
    // x2=x1<<1+x1
    ecp_sm2z256_sqr_mont(x2, x1);
    ecp_sm2z256_mul_mont(x2, x2, x1);
    // x4=x2<<2+x2
    ecp_sm2z256_sqr_mont(x4, x2);
    ecp_sm2z256_sqr_mont(x4, x4);
    ecp_sm2z256_mul_mont(x4, x4, x2);
    // x6=x4<<2+x2
    ecp_sm2z256_sqr_mont(x6, x4);
    ecp_sm2z256_sqr_mont(x6, x6);
    ecp_sm2z256_mul_mont(x6, x6, x2);
    // x12=x6<<6+x6
    ecp_sm2z256_sqr_mont(x12, x6);
    for(i = 0; i < 5; i++)
        ecp_sm2z256_sqr_mont(x12, x12);
    ecp_sm2z256_mul_mont(x12, x12, x6);
    // x24=x12<<12+x12
    ecp_sm2z256_sqr_mont(x24, x12);
    for(i = 0; i < 11; i++)
        ecp_sm2z256_sqr_mont(x24, x24);
    ecp_sm2z256_mul_mont(x24, x24, x12);
    // x30=x24<<6+x6
    ecp_sm2z256_sqr_mont(x30, x32);
    for(i = 0; i < 5; i++)
        ecp_sm2z256_sqr_mont(x30, x30);
    ecp_sm2z256_mul_mont(x30, x30, x6);
    // x31=x30<<1+x1
    ecp_sm2z256_sqr_mont(x31, x30);
    ecp_sm2z256_mul_mont(x31, x31, x1);
    // x32=x30<<2+x2
    ecp_sm2z256_sqr_mont(x32, x31);
    ecp_sm2z256_mul_mont(x32, x32, x1);
    #undef x1
    #undef x2
    #undef x4
    #undef x6
    #undef x12
    #undef x24
    // x31<<33+x32
    for(i = 0; i < 33; i++)
        ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_mul_mont(x31, x31, x32);
    // x31<<32+32
    for(i = 0; i < 32; i++)
        ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_mul_mont(x31, x31, x32);
    // x31<<32+32
    for(i = 0; i < 32; i++)
        ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_mul_mont(x31, x31, x32);
    // x31<<32+32
    for(i = 0; i < 32; i++)
        ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_mul_mont(x31, x31, x32);
    // x31<<64+32
    for(i = 0; i < 64; i++)
        ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_mul_mont(x31, x31, x32);
    // x31<<30+x30
    for(i = 0; i < 30; i++)
        ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_mul_mont(x31, x31, x30);
    // x31<<2
    ecp_sm2z256_sqr_mont(x31, x31);
    ecp_sm2z256_sqr_mont(x31, x31);
    #undef x31
}

/*
 * ecp_sm2z256_bignum_to_field_elem copies the contents of |in| to |out| and
 * returns one if it fits. Otherwise it returns zero.
 */
__owur static int ecp_sm2z256_bignum_to_field_elem(BN_ULONG out[P256_LIMBS],
                                                    const BIGNUM *in)
{
    return bn_copy_words(out, in, P256_LIMBS);
}

# define WINDOWS_SIZE_UNFIXED 5

# define SUB_TABLE_SIZE (1<<(WINDOWS_SIZE_UNFIXED-1))
# if (WINDOWS_SIZE_UNFIXED == 5)
# elif (WINDOWS_SIZE_UNFIXED == 6)
# define ecp_sm2z256_scatter_w5 ecp_sm2z256_scatter_w6
# define ecp_sm2z256_gather_w5 ecp_sm2z256_gather_w6
# define _booth_recode_w5 _booth_recode_w6
# endif

/* r = sum(scalar[i]*point[i]) */
__owur static int ecp_sm2z256_windowed_mul(const EC_GROUP *group,
                                            P256_POINT *r,
                                            const BIGNUM **scalar,
                                            const EC_POINT **point,
                                            size_t num, BN_CTX *ctx)
{
    size_t i;
    int j, ret = 0;
    unsigned int idx;
    // (*p_str) is the uncertain-amount first-dimension, [33] is the certain-amount second-dimension
    unsigned char (*p_str)[33] = NULL;
    unsigned int wvalue;
    P256_POINT *temp;           /* place for 5 temporary points */
    const BIGNUM **scalars = NULL;
    void *table_storage = NULL;
    P256_POINT (*table)[SUB_TABLE_SIZE] = NULL;
    const unsigned int window_size = WINDOWS_SIZE_UNFIXED;
    const unsigned int mask = (1 << (window_size + 1)) - 1;

    // malloc memory for table, p_str, scalars
    // for windows_size = 5 we need extra 5 points for temporary usage
    // for windows_size = 7 we need extra 9 points for temporary usage
    if ((num * SUB_TABLE_SIZE + 6) > OPENSSL_MALLOC_MAX_NELEMS(P256_POINT)
        || (table_storage =
            OPENSSL_malloc((num * SUB_TABLE_SIZE + 9) * sizeof(P256_POINT) + 64)) == NULL
        || (p_str =
            OPENSSL_malloc(num * 33 * sizeof(unsigned char))) == NULL
        || (scalars = OPENSSL_malloc(num * sizeof(BIGNUM *))) == NULL) {
        ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
        goto err;
    }

    table = (void *)ALIGNPTR(table_storage, 64);
    // num is added to the first dimension
    // temp[0-5] is used as temporary values
    temp = (P256_POINT *)(table + num);

    for (i = 0; i < num; i++) {
        P256_POINT *row = table[i];

        /* This is an unusual input, we don't guarantee constant-timeness. */
        if ((BN_num_bits(scalar[i]) > 256) || BN_is_negative(scalar[i])) {
            BIGNUM *mod;

            if ((mod = BN_CTX_get(ctx)) == NULL)
                goto err;
            if (!BN_nnmod(mod, scalar[i], group->order, ctx)) {
                ERR_raise(ERR_LIB_EC, ERR_R_BN_LIB);
                goto err;
            }
            scalars[i] = mod;
        } else
            scalars[i] = scalar[i];

        for (j = 0; j < bn_get_top(scalars[i]) * BN_BYTES; j += BN_BYTES) {
            BN_ULONG d = bn_get_words(scalars[i])[j / BN_BYTES];

            p_str[i][j + 0] = (unsigned char)d;
            p_str[i][j + 1] = (unsigned char)(d >> 8);
            p_str[i][j + 2] = (unsigned char)(d >> 16);
            p_str[i][j + 3] = (unsigned char)(d >>= 24);    // d = d >> 24
            if (BN_BYTES == 8) {
                d >>= 8;
                p_str[i][j + 4] = (unsigned char)d;
                p_str[i][j + 5] = (unsigned char)(d >> 8);
                p_str[i][j + 6] = (unsigned char)(d >> 16);
                p_str[i][j + 7] = (unsigned char)(d >> 24);
            }
        }
        for (; j < 33; j++)
            p_str[i][j] = 0;

        if (!ecp_sm2z256_bignum_to_field_elem(temp[0].X, point[i]->X)
            || !ecp_sm2z256_bignum_to_field_elem(temp[0].Y, point[i]->Y)
            || !ecp_sm2z256_bignum_to_field_elem(temp[0].Z, point[i]->Z)) {
            ERR_raise(ERR_LIB_EC, EC_R_COORDINATES_OUT_OF_RANGE);
            goto err;
        }

        /*
         * row[0] is implicitly (0,0,0) (the point at infinity), therefore it
         * is not stored. All other values are actually stored with an offset
         * of -1 in table.
         */
        // temp[0] is P
        ecp_sm2z256_scatter_w5  (row, &temp[0], 1);
        // temp[1] is 2P
        ecp_sm2z256_point_double(&temp[1], &temp[0]);              /*1+1=2  */
        ecp_sm2z256_scatter_w5  (row, &temp[1], 2);
        // temp[2] is 3P
        ecp_sm2z256_point_add   (&temp[2], &temp[1], &temp[0]);    /*2+1=3  */
        ecp_sm2z256_scatter_w5  (row, &temp[2], 3);
        // temp[1] is 4P
        ecp_sm2z256_point_double(&temp[1], &temp[1]);              /*2*2=4  */
        ecp_sm2z256_scatter_w5  (row, &temp[1], 4);
        // temp[2] is 6P
        ecp_sm2z256_point_double(&temp[2], &temp[2]);              /*2*3=6  */
        ecp_sm2z256_scatter_w5  (row, &temp[2], 6);
        // temp[3] is 5P
        ecp_sm2z256_point_add   (&temp[3], &temp[1], &temp[0]);    /*4+1=5  */
        ecp_sm2z256_scatter_w5  (row, &temp[3], 5);
        // temp[4] is 7P
        ecp_sm2z256_point_add   (&temp[4], &temp[2], &temp[0]);    /*6+1=7  */
        ecp_sm2z256_scatter_w5  (row, &temp[4], 7);

        // now temp[1]=4P, temp[2]=6P, temp[3]=5P, temp[4]=7P
        // temp[1] is 8P
        ecp_sm2z256_point_double(&temp[1], &temp[1]);              /*2*4=8  */
        ecp_sm2z256_scatter_w5  (row, &temp[1], 8);
        // temp[2] is 12P
        ecp_sm2z256_point_double(&temp[2], &temp[2]);              /*2*6=12 */
        ecp_sm2z256_scatter_w5  (row, &temp[2], 12);
        // temp[3] is 10P
        ecp_sm2z256_point_double(&temp[3], &temp[3]);              /*2*5=10 */
        ecp_sm2z256_scatter_w5  (row, &temp[3], 10);
        // temp[4] is 14P
        ecp_sm2z256_point_double(&temp[4], &temp[4]);              /*2*7=14 */
        ecp_sm2z256_scatter_w5  (row, &temp[4], 14);

# if (WINDOWS_SIZE_UNFIXED == 5)
        // now temp[1]=8P, temp[2]=12P, temp[3]=10P, temp[4]=14P
        // temp[2] is 13P
        ecp_sm2z256_point_add   (&temp[2], &temp[2], &temp[0]);    /*12+1=13*/
        ecp_sm2z256_scatter_w5  (row, &temp[2], 13);
        // temp[3] is 11P
        ecp_sm2z256_point_add   (&temp[3], &temp[3], &temp[0]);    /*10+1=11*/
        ecp_sm2z256_scatter_w5  (row, &temp[3], 11);
        // temp[4] is 15P
        ecp_sm2z256_point_add   (&temp[4], &temp[4], &temp[0]);    /*14+1=15*/
        ecp_sm2z256_scatter_w5  (row, &temp[4], 15);
        // temp[2] is 9P
        ecp_sm2z256_point_add   (&temp[2], &temp[1], &temp[0]);    /*8+1=9  */
        ecp_sm2z256_scatter_w5  (row, &temp[2], 9);
        // temp[1] is 16P
        ecp_sm2z256_point_double(&temp[1], &temp[1]);              /*2*8=16 */
        ecp_sm2z256_scatter_w5  (row, &temp[1], 16);
        // now temp[0] = P, temp[1] = 16P, temp[2] = 9p, temp[3] = 11P, temp[4] = 15P
# elif (WINDOWS_SIZE_UNFIXED == 6)
        // now temp[1]=8P, temp[2]=12P, temp[3]=10P, temp[4]=14P
        // we will compute temp[5]=9P, temp[6]=11P, temp[7]=13P, temp[8]=15P
        // temp[5]=9P=8P+1P
        ecp_sm2z256_point_add(&temp[5], &temp[1], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[5], 9);
        // temp[6]=11P=10P+1P
        ecp_sm2z256_point_add(&temp[6], &temp[3], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[6], 11);
        // temp[7]=13P=12P+1P
        ecp_sm2z256_point_add(&temp[7], &temp[2], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[7], 13);
        // temp[8]=15P=14P+1P
        ecp_sm2z256_point_add(&temp[8], &temp[4], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[8], 15);
        // we will compute 16,32,17,18,19,...,31
        // temp[1]=8P*2=16P
        ecp_sm2z256_point_double(&temp[1], &temp[1]);
        ecp_sm2z256_scatter_w5(row, &temp[1], 16);
        // temp[5]=9P*2=18P
        ecp_sm2z256_point_double(&temp[5], &temp[5]);
        ecp_sm2z256_scatter_w5(row, &temp[5], 18);
        // temp[5]=18P+1P=19P
        ecp_sm2z256_point_add(&temp[5], &temp[5], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[5], 19);
        // temp[5]=16P+1P=17P
        ecp_sm2z256_point_add(&temp[5], &temp[1], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[5], 17);
        // temp[5]=16P*2=32P
        ecp_sm2z256_point_double(&temp[5], &temp[1]);
        ecp_sm2z256_scatter_w5(row, &temp[5], 32);
        // temp[3]=10P*2=20P
        ecp_sm2z256_point_double(&temp[3], &temp[3]);
        ecp_sm2z256_scatter_w5(row, &temp[3], 20);
        // temp[3]=20P+1P=21P
        ecp_sm2z256_point_add(&temp[3], &temp[3], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[3], 21);
        // temp[6]=11P*2=22P
        ecp_sm2z256_point_double(&temp[6], &temp[6]);
        ecp_sm2z256_scatter_w5(row, &temp[6], 22);
        // temp[6]=22P+1P=23P
        ecp_sm2z256_point_add(&temp[6], &temp[6], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[6], 23);
        // temp[2]=12P*2=24P
        ecp_sm2z256_point_double(&temp[2], &temp[2]);
        ecp_sm2z256_scatter_w5(row, &temp[2], 24);
        // temp[2]=24P+1P=25P
        ecp_sm2z256_point_add(&temp[2], &temp[2], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[2], 25);
        // temp[7]=13P*2=26P
        ecp_sm2z256_point_double(&temp[7], &temp[7]);
        ecp_sm2z256_scatter_w5(row, &temp[7], 26);
        // temp[7]=26P+1P=27P
        ecp_sm2z256_point_add(&temp[7], &temp[7], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[7], 27);
        // temp[4]=14P*2=28P
        ecp_sm2z256_point_double(&temp[4], &temp[4]);
        ecp_sm2z256_scatter_w5(row, &temp[4], 28);
        // temp[4]=28P+1P
        ecp_sm2z256_point_add(&temp[4], &temp[4], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[4], 29);
        // temp[8]=15P*2=30P
        ecp_sm2z256_point_double(&temp[8], &temp[8]);
        ecp_sm2z256_scatter_w5(row, &temp[8], 30);
        // temp[8]=30P+1P
        ecp_sm2z256_point_add(&temp[8], &temp[8], &temp[0]);
        ecp_sm2z256_scatter_w5(row, &temp[8], 31);
# endif
    }
    /**
     * For w=5
     * 
     * Why idx = 255? Why (idx - 1) / 8 & (idx - 1) % 8? Why 8?
     * 
     * 8: 8-bit each p_str
     * 
     * idx - 1 means: we will process w-bit windows: 
     * idx-1+w-1, idx-1+w-2, ..., idx-1
     * 
     * 256 % 5 = 1, so we need to firstly handle the booth encode of
     * remaining top 1-bit, i.e., p_str[0][31] >> 6
     * 2-th call booth_encode: p_str[0][31] >> 1
     * 3-th call booth_encode: (p_str[0][31] << 8 | p_str[0][30]) >> 4
     * 
     * why - 1, here 1 = 256 % 5
     * 
     * Maybe, - 1 is because of the property of the booth encoding
     * 
     * idx = 255
     * wvalue = p_str[0][31]
     * wvalue = (wvalue >> 6) & mask, i.e., we will encode the scalar bit 255 & 254
     * booth_recode_w5(wvalue) and gather
     * five r=r^2
     * 
     * idx = 255 - 5 = 250
     * off = (250 - 1) / 8 = 31
     * wvalue = p_str[0][32] << 8 | p_str[0][31] = 0 | p_str[0][31]
     * wvalue = (wvalue >> 1) & mask
     * gather -> conditional neg -> point add
     * 
     * idx = 250 - 5 = 245
     * off = (245 - 1) / 8 = 30
     * wvalue = p_str[0][31] << 8 | p_str[0][30]
     * wvalue = (wvalue >> 4) & mask
     */
    idx = 255;
    wvalue = p_str[0][(idx - (256 % WINDOWS_SIZE_UNFIXED)) / 8];
    wvalue = (wvalue >> ((idx - (256 % WINDOWS_SIZE_UNFIXED)) % 8)) & mask;
    /*
     * We gather to temp[0], because we know it's position relative
     * to table
     * 
     * Here, we process the top-1 bit, so no need to conditional neg
     */
    ecp_sm2z256_gather_w5(&temp[0], table[0], _booth_recode_w5(wvalue) >> 1);
    memcpy(r, &temp[0], sizeof(temp[0]));

    while (idx >= WINDOWS_SIZE_UNFIXED) {
        for (i = (idx == 255 ? 1 : 0); i < num; i++) {
            unsigned int off = (idx - (256 % WINDOWS_SIZE_UNFIXED)) / 8;

            wvalue = p_str[i][off] | p_str[i][off + 1] << 8;
            wvalue = (wvalue >> ((idx - (256 % WINDOWS_SIZE_UNFIXED)) % 8)) & mask;

            wvalue = _booth_recode_w5(wvalue);

            ecp_sm2z256_gather_w5(&temp[0], table[i], wvalue >> 1);

            ecp_sm2z256_neg(temp[1].Y, temp[0].Y);
            copy_conditional(temp[0].Y, temp[1].Y, (wvalue & 1));

            ecp_sm2z256_point_add(r, r, &temp[0]);
        }

        idx -= window_size;

        ecp_sm2z256_point_double(r, r);
        ecp_sm2z256_point_double(r, r);
        ecp_sm2z256_point_double(r, r);
        ecp_sm2z256_point_double(r, r);
        ecp_sm2z256_point_double(r, r);
        # if (WINDOWS_SIZE_UNFIXED == 6)
        ecp_sm2z256_point_double(r, r);
        #endif
    }

    /* Final window */
    for (i = 0; i < num; i++) {
        wvalue = p_str[i][0];
        wvalue = (wvalue << 1) & mask;

        wvalue = _booth_recode_w5(wvalue);

        ecp_sm2z256_gather_w5(&temp[0], table[i], wvalue >> 1);

        ecp_sm2z256_neg(temp[1].Y, temp[0].Y);
        copy_conditional(temp[0].Y, temp[1].Y, wvalue & 1);

        ecp_sm2z256_point_add(r, r, &temp[0]);
    }

    ret = 1;
 err:
    OPENSSL_free(table_storage);
    OPENSSL_free(p_str);
    OPENSSL_free(scalars);
    return ret;
}

# if (WINDOWS_SIZE_UNFIXED == 6)
# undef ecp_sm2z256_gather_w5
# undef ecp_sm2z256_scatter_w5
# undef _booth_recode_w5
# endif

/* Coordinates of G, for which we have precomputed tables */
const static BN_ULONG def_xG[P256_LIMBS] = {
     TOBN(0x61328990, 0xf418029e), TOBN(0x3e7981ed, 0xdca6c050),
     TOBN(0xd6a1ed99, 0xac24c3c3), TOBN(0x91167a5e, 0xe1c13b05)
};

const static BN_ULONG def_yG[P256_LIMBS] = {
     TOBN(0xc1354e59, 0x3c2d0ddd), TOBN(0xc1f5e578, 0x8d3295fa),
     TOBN(0x8d4cfb06, 0x6e2a48f8), TOBN(0x63cd65d4, 0x81d735bd)
};

/*
 * ecp_sm2z256_is_affine_G returns one if |generator| is the standard, P-256
 * generator.
 */
static int ecp_sm2z256_is_affine_G(const EC_POINT *generator)
{
    return (bn_get_top(generator->X) == P256_LIMBS) &&
        (bn_get_top(generator->Y) == P256_LIMBS) &&
        is_equal(bn_get_words(generator->X), def_xG) &&
        is_equal(bn_get_words(generator->Y), def_yG) &&
        is_one(generator->Z);
}

__owur static int ecp_sm2z256_mult_precompute(EC_GROUP *group, BN_CTX *ctx)
{
    /*
     * We precompute a table for a Booth encoded exponent (wNAF) based
     * computation. Each table holds 64 values for safe access, with an
     * implicit value of infinity at index zero. We use window of size 7, and
     * therefore require ceil(256/7) = 37 tables.
     */
    const BIGNUM *order;
    EC_POINT *P = NULL, *T = NULL;
    const EC_POINT *generator;
    SM2Z256_PRE_COMP *pre_comp;
    BN_CTX *new_ctx = NULL;
    int i, j, k, ret = 0;
    size_t w;

    PRECOMP256_ROW *preComputedTable = NULL;
    unsigned char *precomp_storage = NULL;

    /* if there is an old SM2Z256_PRE_COMP object, throw it away */
    EC_pre_comp_free(group);
    generator = EC_GROUP_get0_generator(group);
    if (generator == NULL) {
        ERR_raise(ERR_LIB_EC, EC_R_UNDEFINED_GENERATOR);
        return 0;
    }

    if (ecp_sm2z256_is_affine_G(generator)) {
        /*
         * No need to calculate tables for the standard generator because we
         * have them statically.
         */
        return 1;
    }

    if ((pre_comp = ecp_sm2z256_pre_comp_new(group)) == NULL)
        return 0;

    if (ctx == NULL) {
        ctx = new_ctx = BN_CTX_new_ex(group->libctx);
        if (ctx == NULL)
            goto err;
    }

    BN_CTX_start(ctx);

    order = EC_GROUP_get0_order(group);
    if (order == NULL)
        goto err;

    if (BN_is_zero(order)) {
        ERR_raise(ERR_LIB_EC, EC_R_UNKNOWN_ORDER);
        goto err;
    }

    w = 7;

    if ((precomp_storage =
         OPENSSL_malloc(37 * 64 * sizeof(P256_POINT_AFFINE) + 64)) == NULL) {
        ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
        goto err;
    }

    preComputedTable = (void *)ALIGNPTR(precomp_storage, 64);

    P = EC_POINT_new(group);
    T = EC_POINT_new(group);
    if (P == NULL || T == NULL)
        goto err;

    /*
     * The zero entry is implicitly infinity, and we skip it, storing other
     * values with -1 offset.
     */
    if (!EC_POINT_copy(T, generator))
        goto err;

    // each sub-table has 64 points
    // if we smashes precompute-table (preComputedTable[j]+k) is the address
    // where k-th point's first byte of the sub-table will be stored
    // if we don't smashes precompute-table (preComputedTable[j]+k*64) is the address
    // where k-th point of the sub-table will be stored
    for (k = 0; k < 64; k++) {
        if (!EC_POINT_copy(P, T))
            goto err;
        // there are 37 sub-tables
        for (j = 0; j < 37; j++) {
            P256_POINT_AFFINE temp;
            /*
             * It would be faster to use EC_POINTs_make_affine and
             * make multiple points affine at the same time.
             */
            if (group->meth->make_affine == NULL
                || !group->meth->make_affine(group, P, ctx))
                goto err;
            if (!ecp_sm2z256_bignum_to_field_elem(temp.X, P->X) ||
                !ecp_sm2z256_bignum_to_field_elem(temp.Y, P->Y)) {
                ERR_raise(ERR_LIB_EC, EC_R_COORDINATES_OUT_OF_RANGE);
                goto err;
            }
            ecp_sm2z256_scatter_w7(preComputedTable[j], &temp, k);
            for (i = 0; i < 7; i++) {
                if (!EC_POINT_dbl(group, P, P, ctx))
                    goto err;
            }
        }
        if (!EC_POINT_add(group, T, T, generator, ctx))
            goto err;
    }

    pre_comp->group = group;
    pre_comp->w = w;
    pre_comp->precomp = preComputedTable;
    pre_comp->precomp_storage = precomp_storage;
    precomp_storage = NULL;
    SETPRECOMP(group, sm2z256, pre_comp);
    pre_comp = NULL;
    ret = 1;

 err:
    BN_CTX_end(ctx);
    BN_CTX_free(new_ctx);

    EC_sm2z256_pre_comp_free(pre_comp);
    OPENSSL_free(precomp_storage);
    EC_POINT_free(P);
    EC_POINT_free(T);
    return ret;
}

__owur static int ecp_sm2z256_set_from_affine(EC_POINT *out, const EC_GROUP *group,
                                               const P256_POINT_AFFINE *in,
                                               BN_CTX *ctx)
{
    int ret = 0;

    if ((ret = bn_set_words(out->X, in->X, P256_LIMBS))
        && (ret = bn_set_words(out->Y, in->Y, P256_LIMBS))
        && (ret = bn_set_words(out->Z, ONE, P256_LIMBS)))
        out->Z_is_one = 1;

    return ret;
}

/**
 * @brief computing scalar1*G + scalar2*P，w=4
 * 
 * @param group including computing function and parameters of SM2
 * @param r result point
 * @param scalar1 the scalar of base point G
 * @param point2 another point namely P
 * @param scalar2 the scalar of unfixed point P
 * @param ctx context of big number computing
 */
__owur static int ecp_sm2z256_multi_points_mul(const EC_GROUP *group,
                                                EC_POINT *r,
                                                const BIGNUM *scalar1,
                                                const EC_POINT *point2,
                                                const BIGNUM *scalar2,
                                                BN_CTX *ctx)
{
    int i = 0, ret = 0;
    // char version of the scalar1 and scalar2
    unsigned char s1_str[33] = {0};
    unsigned char s2_str[33] = {0};
    // we used our hardcoded table
    const PRECOMP256_ROW *preComputedTable = ecp_sm2z256_precomputed;
    const EC_POINT *generator = NULL;
    unsigned int idx = 0;
    const unsigned int windows_size = 4;
    const unsigned int mask = (1 << (windows_size + 1)) - 1;
    unsigned int wvalue;
    BN_ULONG infty;
    ALIGN32 union {
        P256_POINT p;           // including X Y Z
        P256_POINT_AFFINE a;    // including X Y
    } t, p;
    // for pre-computed table
    P256_POINT table[16];
    P256_POINT temp[3];

    generator = EC_GROUP_get0_generator(group);

    for (i = 0; i < bn_get_top(scalar1) * BN_BYTES; i += BN_BYTES) {
        // i-th word of scalar1 and scalar2
        BN_ULONG d1 = bn_get_words(scalar1)[i / BN_BYTES];
        BN_ULONG d2 = bn_get_words(scalar2)[i / BN_BYTES];
        // for scalar1
        s1_str[i + 0] = (unsigned char)d1;
        s1_str[i + 1] = (unsigned char)(d1 >> 8);
        s1_str[i + 2] = (unsigned char)(d1 >> 16);
        s1_str[i + 3] = (unsigned char)(d1 >>= 24);
        // for scalar2
        s2_str[i + 0] = (unsigned char)d2;
        s2_str[i + 1] = (unsigned char)(d2 >> 8);
        s2_str[i + 2] = (unsigned char)(d2 >> 16);
        s2_str[i + 3] = (unsigned char)(d2 >>= 24);
        if (BN_BYTES == 8) {
            d1 >>= 8;
            d2 >>= 8;
            s1_str[i + 4] = (unsigned char)d1;
            s1_str[i + 5] = (unsigned char)(d1 >> 8);
            s1_str[i + 6] = (unsigned char)(d1 >> 16);
            s1_str[i + 7] = (unsigned char)(d1 >> 24);
            s2_str[i + 4] = (unsigned char)d2;
            s2_str[i + 5] = (unsigned char)(d2 >> 8);
            s2_str[i + 6] = (unsigned char)(d2 >> 16);
            s2_str[i + 7] = (unsigned char)(d2 >> 24);
        }
    }
    for (; i < 33; i++) {
        s1_str[i] = 0;
        s2_str[i] = 0;
    }

    if (!ecp_sm2z256_bignum_to_field_elem(temp[0].X, point2->X)
        || !ecp_sm2z256_bignum_to_field_elem(temp[0].Y, point2->Y)
        || !ecp_sm2z256_bignum_to_field_elem(temp[0].Z, point2->Z)) {
        ERR_raise(ERR_LIB_EC, EC_R_COORDINATES_OUT_OF_RANGE);
        goto err;
    }

    /**
     * Now, we want to pre-compute jG+kQ for j, k in [1, 8]
     * jG+kQ is stored into table[i*8]
     * 
     */

err:
    return ret;
}

/* num=0, points=NULL, scalars=NULL when computing scalar*G */
/**
 * @brief r = scalar*G + sum(scalars[i]*points[i])
 * 
 * @param group 包含椭圆曲线运算方法、椭圆曲线参数等信息
 * @param r 结果
 * @param scalar 标量
 * @param num 计算标量乘累加时的标量数量
 * @param points 计算标量乘累加时的num个点
 * @param scalars 计算标量乘累加时的num个标量
 * @param ctx 大整数相关设置的上下文
 */
__owur static int ecp_sm2z256_points_mul(const EC_GROUP *group,
                                          EC_POINT *r,
                                          const BIGNUM *scalar,
                                          size_t num,
                                          const EC_POINT *points[],
                                          const BIGNUM *scalars[], BN_CTX *ctx)
{
    int i = 0, ret = 0, no_precomp_for_generator = 0, p_is_infinity = 0;
    // p_str[i]指向标量的第i个byte
    unsigned char p_str[33] = { 0 };
    // one row includes 64 points
    const PRECOMP256_ROW *preComputedTable = NULL;
    const SM2Z256_PRE_COMP *pre_comp = NULL;
    const EC_POINT *generator = NULL;
    const BIGNUM **new_scalars = NULL;
    const EC_POINT **new_points = NULL;
    unsigned int idx = 0;
    // 滑动窗口，窗口的大小
    const unsigned int window_size = 7;
    // 2^8 - 1 = 0xff
    const unsigned int mask = (1 << (window_size + 1)) - 1;
    unsigned int wvalue;
    ALIGN32 union {
        P256_POINT p;           // including X Y Z
        P256_POINT_AFFINE a;    // including X Y
    } t, p;
    BIGNUM *tmp_scalar;

    // 检查 num 的合理性
    if ((num + 1) == 0 || (num + 1) > OPENSSL_MALLOC_MAX_NELEMS(void *)) {
        ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
        return 0;
    }
    // 用于分配空间和debug
    BN_CTX_start(ctx);
    // 计算固定点标量乘
    if (scalar) {
        // get base point
        generator = EC_GROUP_get0_generator(group);
        if (generator == NULL) {
            ERR_raise(ERR_LIB_EC, EC_R_UNDEFINED_GENERATOR);
            goto err;
        }
        // 没有走该分支，走的下面的分支
        /* look if we can use precomputed multiples of generator */
        pre_comp = group->pre_comp.sm2z256;
        if (pre_comp) {
            /*
             * If there is a precomputed table for the generator, check that
             * it was generated with the same generator.
             */
            EC_POINT *pre_comp_generator = EC_POINT_new(group);
            if (pre_comp_generator == NULL)
                goto err;

            ecp_sm2z256_gather_w7(&p.a, pre_comp->precomp[0], 1);
            if (!ecp_sm2z256_set_from_affine(pre_comp_generator,
                                              group, &p.a, ctx)) {
                EC_POINT_free(pre_comp_generator);
                goto err;
            }

            if (0 == EC_POINT_cmp(group, generator, pre_comp_generator, ctx))
                preComputedTable = (const PRECOMP256_ROW *)pre_comp->precomp;

            EC_POINT_free(pre_comp_generator);
        }
        // 给预计算表赋值
        if (preComputedTable == NULL && ecp_sm2z256_is_affine_G(generator)) {
            /*
             * If there is no precomputed data, but the generator is the
             * default, a hardcoded table of precomputed data is used. This
             * is because applications, such as Apache, do not use
             * EC_KEY_precompute_mult.
             */
            preComputedTable = ecp_sm2z256_precomputed;
        }
        // 使用的是我们硬编码的预计算表
        if (preComputedTable) {
            BN_ULONG infty;
            // 如果标量过长 或 为负数，进行模运算处理
            if ((BN_num_bits(scalar) > 256)
                || BN_is_negative(scalar)) {
                if ((tmp_scalar = BN_CTX_get(ctx)) == NULL)
                    goto err;

                if (!BN_nnmod(tmp_scalar, scalar, group->order, ctx)) {
                    ERR_raise(ERR_LIB_EC, ERR_R_BN_LIB);
                    goto err;
                }
                scalar = tmp_scalar;
            }
            /**
             * Here, if num == 1, we call our multi-point scalar mul function,
             * set ret, and goto err label
             */

            // if (!ecp_sm2z256_multi_points_mul(group, r, scalar, points[0], scalars[0], ctx)){
            //     goto err;
            // }

            // for sm2, bn_get_top(scalar) returns 4, BN_BYTES = 8 on 64-bit machine
            // 256-bit scalar == 4 * 8 Bytes == 4 * BN_BYTES Bytes == 32 Bytes
            // i = 0, 8, 16, 24
            // this loop set 32-byte word-points to 32 Bytes of 256-bit scalar
            // p_str[i]指向标量的第i个byte
            for (i = 0; i < bn_get_top(scalar) * BN_BYTES; i += BN_BYTES) {
                // i-th word of scalar
                BN_ULONG d = bn_get_words(scalar)[i / BN_BYTES];

                p_str[i + 0] = (unsigned char)d;
                p_str[i + 1] = (unsigned char)(d >> 8);
                p_str[i + 2] = (unsigned char)(d >> 16);
                p_str[i + 3] = (unsigned char)(d >>= 24);
                if (BN_BYTES == 8) {
                    d >>= 8;
                    p_str[i + 4] = (unsigned char)d;
                    p_str[i + 5] = (unsigned char)(d >> 8);
                    p_str[i + 6] = (unsigned char)(d >> 16);
                    p_str[i + 7] = (unsigned char)(d >> 24);
                }
            }
            // 标量长256bit = 32*8 bit，后面置0
            for (; i < 33; i++)
                p_str[i] = 0;

            /* First 7-bit window */
            // 这里左移了一位，是为了booth编码
            wvalue = (p_str[0] << 1) & mask;
            idx += window_size;
            // 对前7bit进行booth编码，wvalue的最低位为符号位、其余位为绝对值
            wvalue = _booth_recode_w7(wvalue);
            // 取预计算点，保存到p中
            ecp_sm2z256_gather_w7(&p.a, preComputedTable[0],
                                   wvalue >> 1);
            // 根据wvalue的符号位决定是否对点的Y值取负
            ecp_sm2z256_neg(p.p.Z, p.p.Y);
            copy_conditional(p.p.Y, p.p.Z, wvalue & 1);

            /*
             * Since affine infinity is encoded as (0,0) and
             * Jacobian is (,,0), we need to harmonize them
             * by assigning "one" or zero to Z.
             */
            infty = (p.p.X[0] | p.p.X[1] | p.p.X[2] | p.p.X[3] |
                     p.p.Y[0] | p.p.Y[1] | p.p.Y[2] | p.p.Y[3]);
            if (P256_LIMBS == 8)
                infty |= (p.p.X[4] | p.p.X[5] | p.p.X[6] | p.p.X[7] |
                          p.p.Y[4] | p.p.Y[5] | p.p.Y[6] | p.p.Y[7]);

            infty = 0 - is_zero(infty);
            infty = ~infty;

            p.p.Z[0] = ONE[0] & infty;
            p.p.Z[1] = ONE[1] & infty;
            p.p.Z[2] = ONE[2] & infty;
            p.p.Z[3] = ONE[3] & infty;
            if (P256_LIMBS == 8) {
                p.p.Z[4] = ONE[4] & infty;
                p.p.Z[5] = ONE[5] & infty;
                p.p.Z[6] = ONE[6] & infty;
                p.p.Z[7] = ONE[7] & infty;
            }

            for (i = 1; i < 37; i++) {
                // 再次构造booth编码的输入
                unsigned int off = (idx - 1) / 8;
                wvalue = p_str[off] | p_str[off + 1] << 8;
                wvalue = (wvalue >> ((idx - 1) % 8)) & mask;
                idx += window_size;
                // 计算booth编码，并根据值取预计算表项
                wvalue = _booth_recode_w7(wvalue);
                ecp_sm2z256_gather_w7(&t.a,
                                       preComputedTable[i], wvalue >> 1);
                ecp_sm2z256_neg(t.p.Z, t.a.Y);
                copy_conditional(t.a.Y, t.p.Z, wvalue & 1);
                // 预计算表中包含了G^(2^window_size)，无需在此处计算p.p^(2^window_size)
                ecp_sm2z256_point_add_affine(&p.p, &p.p, &t.a);
            }
        } else {
            p_is_infinity = 1;
            no_precomp_for_generator = 1;
        }
    } else
        p_is_infinity = 1;

    // 对于固定点算法 且 没有预计算表的情况下走该分支
    // 将标量和点放到new_scalars 和 new_points数组里
    if (no_precomp_for_generator) {
        /*
         * Without a precomputed table for the generator, it has to be
         * handled like a normal point.
         */
        new_scalars = OPENSSL_malloc((num + 1) * sizeof(BIGNUM *));
        if (new_scalars == NULL) {
            ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
            goto err;
        }

        new_points = OPENSSL_malloc((num + 1) * sizeof(EC_POINT *));
        if (new_points == NULL) {
            ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
            goto err;
        }

        memcpy(new_scalars, scalars, num * sizeof(BIGNUM *));
        new_scalars[num] = scalar;
        memcpy(new_points, points, num * sizeof(EC_POINT *));
        new_points[num] = generator;

        scalars = new_scalars;
        points = new_points;
        num++;
    }
    // 如果要计算额外的标量乘并累加，则调用ecp_sm2z256_windowed_mul函数
    if (num) {
        P256_POINT *out = &t.p;
        if (p_is_infinity)
            out = &p.p;

        if (!ecp_sm2z256_windowed_mul(group, out, scalars, points, num, ctx))
            goto err;

        if (!p_is_infinity)
            ecp_sm2z256_point_add(&p.p, &p.p, out);
    }

    /* Not constant-time, but we're only operating on the public output. */
    if (!bn_set_words(r->X, p.p.X, P256_LIMBS) ||
        !bn_set_words(r->Y, p.p.Y, P256_LIMBS) ||
        !bn_set_words(r->Z, p.p.Z, P256_LIMBS)) {
        goto err;
    }
    r->Z_is_one = is_one(r->Z) & 1;

    ret = 1;

err:
    BN_CTX_end(ctx);
    OPENSSL_free(new_points);
    OPENSSL_free(new_scalars);
    return ret;
}

__owur static int ecp_sm2z256_get_affine(const EC_GROUP *group,
                                          const EC_POINT *point,
                                          BIGNUM *x, BIGNUM *y, BN_CTX *ctx)
{
    BN_ULONG z_inv2[P256_LIMBS];
    BN_ULONG z_inv3[P256_LIMBS];
    BN_ULONG x_aff[P256_LIMBS];
    BN_ULONG y_aff[P256_LIMBS];
    BN_ULONG point_x[P256_LIMBS], point_y[P256_LIMBS], point_z[P256_LIMBS];
    BN_ULONG x_ret[P256_LIMBS], y_ret[P256_LIMBS];

    if (EC_POINT_is_at_infinity(group, point)) {
        ERR_raise(ERR_LIB_EC, EC_R_POINT_AT_INFINITY);
        return 0;
    }

    if (!ecp_sm2z256_bignum_to_field_elem(point_x, point->X) ||
        !ecp_sm2z256_bignum_to_field_elem(point_y, point->Y) ||
        !ecp_sm2z256_bignum_to_field_elem(point_z, point->Z)) {
        ERR_raise(ERR_LIB_EC, EC_R_COORDINATES_OUT_OF_RANGE);
        return 0;
    }

    // ecp_sm2z256_mod_inverse(z_inv3, point_z);
    // ecp_sm2z256_sqr_mont(z_inv2, z_inv3);
    // z^-2
    ecp_sm2z256_mod_inverse_sqr(z_inv2, point_z);
    ecp_sm2z256_mul_mont(x_aff, z_inv2, point_x);

    if (x != NULL) {
        ecp_sm2z256_from_mont(x_ret, x_aff);
        if (!bn_set_words(x, x_ret, P256_LIMBS))
            return 0;
    }

    if (y != NULL) {
        // ecp_sm2z256_mul_mont(z_inv3, z_inv3, z_inv2);
        // z^-4
        ecp_sm2z256_sqr_mont(z_inv3, z_inv2);
        // z^-3
        ecp_sm2z256_mul_mont(z_inv3, z_inv3, point_z);
        ecp_sm2z256_mul_mont(y_aff, z_inv3, point_y);
        ecp_sm2z256_from_mont(y_ret, y_aff);
        if (!bn_set_words(y, y_ret, P256_LIMBS))
            return 0;
    }

    return 1;
}

static SM2Z256_PRE_COMP *ecp_sm2z256_pre_comp_new(const EC_GROUP *group)
{
    SM2Z256_PRE_COMP *ret = NULL;

    if (!group)
        return NULL;

    ret = OPENSSL_zalloc(sizeof(*ret));

    if (ret == NULL) {
        ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
        return ret;
    }

    ret->group = group;
    ret->w = 6;                 /* default */
    ret->references = 1;

    ret->lock = CRYPTO_THREAD_lock_new();
    if (ret->lock == NULL) {
        ERR_raise(ERR_LIB_EC, ERR_R_MALLOC_FAILURE);
        OPENSSL_free(ret);
        return NULL;
    }
    return ret;
}

SM2Z256_PRE_COMP *EC_sm2z256_pre_comp_dup(SM2Z256_PRE_COMP *p)
{
    int i;
    if (p != NULL)
        CRYPTO_UP_REF(&p->references, &i, p->lock);
    return p;
}

void EC_sm2z256_pre_comp_free(SM2Z256_PRE_COMP *pre)
{
    int i;

    if (pre == NULL)
        return;

    CRYPTO_DOWN_REF(&pre->references, &i, pre->lock);
    REF_PRINT_COUNT("EC_sm2z256", pre);
    if (i > 0)
        return;
    REF_ASSERT_ISNT(i < 0);

    OPENSSL_free(pre->precomp_storage);
    CRYPTO_THREAD_lock_free(pre->lock);
    OPENSSL_free(pre);
}


static int ecp_sm2z256_window_have_precompute_mult(const EC_GROUP *group)
{
    /* There is a hard-coded table for the default generator. */
    const EC_POINT *generator = EC_GROUP_get0_generator(group);

    if (generator != NULL && ecp_sm2z256_is_affine_G(generator)) {
        /* There is a hard-coded table for the default generator. */
        return 1;
    }

    return HAVEPRECOMP(group, sm2z256);
}

#if defined(__x86_64) || defined(__x86_64__) || \
    defined(_M_AMD64) || defined(_M_X64) || \
    defined(__powerpc64__) || defined(_ARCH_PP64) || \
    defined(__aarch64__)
/*
 * Montgomery mul modulo Order(P): res = a*b*2^-256 mod Order(P)
 */
void ecp_sm2z256_ord_mul_mont(BN_ULONG res[P256_LIMBS],
                               const BN_ULONG a[P256_LIMBS],
                               const BN_ULONG b[P256_LIMBS]);
void ecp_sm2z256_ord_sqr_mont(BN_ULONG res[P256_LIMBS],
                               const BN_ULONG a[P256_LIMBS],
                               BN_ULONG rep);

static int ecp_sm2z256_inv_mod_ord(const EC_GROUP *group, BIGNUM *r,
                                    const BIGNUM *x, BN_CTX *ctx)
{
    /* RR = 2^512 mod ord(sm2) */
    static const BN_ULONG RR[P256_LIMBS]  = {
        TOBN(0x901192af,0x7c114f20), TOBN(0x3464504a,0xde6fa2fa),
        TOBN(0x620fc84c,0x3affe0d4), TOBN(0x1eb5e412,0xa22b3d3b)
    };
    /* The constant 1 (unlike ONE that is one in Montgomery representation) */
    static const BN_ULONG one[P256_LIMBS] = {
        TOBN(0,1), TOBN(0,0), TOBN(0,0), TOBN(0,0)
    };
    /*
     * We don't use entry 0 in the table, so we omit it and address
     * with -1 offset.
     */
    BN_ULONG out[P256_LIMBS], t[P256_LIMBS];
    int i, ret = 0;

    /*
     * Catch allocation failure early.
     */
    if (bn_wexpand(r, P256_LIMBS) == NULL) {
        ERR_raise(ERR_LIB_EC, ERR_R_BN_LIB);
        goto err;
    }

    if ((BN_num_bits(x) > 256) || BN_is_negative(x)) {
        BIGNUM *tmp;

        if ((tmp = BN_CTX_get(ctx)) == NULL
            || !BN_nnmod(tmp, x, group->order, ctx)) {
            ERR_raise(ERR_LIB_EC, ERR_R_BN_LIB);
            goto err;
        }
        x = tmp;
    }

    if (!ecp_sm2z256_bignum_to_field_elem(t, x)) {
        ERR_raise(ERR_LIB_EC, EC_R_COORDINATES_OUT_OF_RANGE);
        goto err;
    }
#if 0
    /**
     * overhead:
     * mul: 1+8+10+32-3+1=49
     * dbl: 8+124+128=260
     */
    BN_ULONG table[15][P256_LIMBS];
    BN_ULONG t2[P256_LIMBS];
    // trans to mont field
    ecp_sm2z256_ord_mul_mont(table[0], t, RR);
    /*
     * Original sparse-then-fixed-window algorithm, retained for reference.
     * table[1]=_10, table[2]=_11, ...
     */
    for (i = 2; i < 16; i += 2) {
        ecp_sm2z256_ord_sqr_mont(table[i-1], table[i/2-1], 1);
        ecp_sm2z256_ord_mul_mont(table[i], table[i-1], table[0]);
    }

    /*
     * The top 128bit of the exponent are highly redudndant, so we
     * perform an optimized flow
     */
    ecp_sm2z256_ord_sqr_mont(t, table[15-1], 4);   /* f0 */
    ecp_sm2z256_ord_mul_mont(t2, t, table[14-1]);  /* fe */
    ecp_sm2z256_ord_mul_mont(t, t, table[15-1]);   /* ff */

    ecp_sm2z256_ord_sqr_mont(out, t, 8);           /* ff00 */
    ecp_sm2z256_ord_mul_mont(t2, out, t2);         /* fffe */
    ecp_sm2z256_ord_mul_mont(out, out, t);         /* ffff */

    ecp_sm2z256_ord_sqr_mont(t, out, 16);          /* ffff0000 */
    ecp_sm2z256_ord_mul_mont(t, t, t2);            /* fffffffe */
    ecp_sm2z256_ord_mul_mont(t2, t, table[1-1]);   /* ffffffff */

    ecp_sm2z256_ord_sqr_mont(out, t, 32);          /* fffffffe00000000 */
    ecp_sm2z256_ord_mul_mont(out, out, t2);        /* fffffffeffffffff */
    ecp_sm2z256_ord_mul_mont(t, out, table[1-1]);  /* ffffffff00000000 */
    ecp_sm2z256_ord_mul_mont(t, t, t2);            /* ffffffffffffffff */

    ecp_sm2z256_ord_sqr_mont(out, out, 64);        /* fffffffeffffffff0000000000000000 */
    ecp_sm2z256_ord_mul_mont(out, out, t);         /* fffffffeffffffffffffffffffffffff */

    /*
     * The bottom 128 bit of the exponent are processed with fixed 4-bit window
     */
    for(i = 0; i < 32; i++) {
        /* expLo - the low 128 bits of the exponent we use (ord(sm2) - 2),
         * split into nibbles */
        static const unsigned char expLo[32]  = {
            0x7,0x2,0x0,0x3,0xd,0xf,0x6,0xb,0x2,0x1,0xc,0x6,0x0,0x5,0x2,0xb,
            0x5,0x3,0xb,0xb,0xf,0x4,0x0,0x9,0x3,0x9,0xd,0x5,0x4,0x1,0x2,0x1
        };

        ecp_sm2z256_ord_sqr_mont(out, out, 4);
        /* The exponent is public, no need in constant-time access */
        if (expLo[i] != 0)
            ecp_sm2z256_ord_mul_mont(out, out, table[expLo[i]-1]);
    }
#else
    /**
     * Overhead:
     * mul: 1+16+25+1=43
     * dbl: 57+192=249
     */
    BN_ULONG table[11][P256_LIMBS];
    enum {
        i_1 = 0, i_11,     i_101, i_111, i_1001, i_1011, i_1111,
        i_10101, i_11111,  i_x31, i_x32
    };
    // trans to mont field
    ecp_sm2z256_ord_mul_mont(table[0], t, RR);
    /*
     * https://briansmith.org/ecc-inversion-addition-chains-01#p256_scalar_inversion
     *
     * Even though this code path spares 12 squarings, 4.5%, and 13
     * multiplications, 25%, on grand scale sign operation is not that
     * much faster, not more that 2%...
     */

    /* pre-calculate powers */
    // t=i_10=i_1<<1
    ecp_sm2z256_ord_sqr_mont(t, table[i_1], 1);
    // i_11=i_10+i_1
    ecp_sm2z256_ord_mul_mont(table[i_11], t, table[i_1]);
    // i_101=i_10+i_11
    ecp_sm2z256_ord_mul_mont(table[i_101], t, table[i_11]);
    // i_111=i_10+i_101
    ecp_sm2z256_ord_mul_mont(table[i_111], t, table[i_101]);
    // i_1001=i_10<<2+i_1
    ecp_sm2z256_ord_sqr_mont(table[i_1001], t, 2);
    ecp_sm2z256_ord_mul_mont(table[i_1001], table[i_1001], table[i_1]);
    // t=i_1010=i_101<<1
    ecp_sm2z256_ord_sqr_mont(t, table[i_101], 1);
    // i_1011=i_1010+i_1
    ecp_sm2z256_ord_mul_mont(table[i_1011], t, table[i_1]);
    // i_1111=i_1010+i_101
    ecp_sm2z256_ord_mul_mont(table[i_1111], t, table[i_101]);
    // i_10101=i_1010<<1+i_1
    ecp_sm2z256_ord_sqr_mont(table[i_10101], t, 1);
    ecp_sm2z256_ord_mul_mont(table[i_10101], table[i_10101], table[i_1]);
    // i_11111=i_10101+i_1010
    ecp_sm2z256_ord_mul_mont(table[i_11111], table[i_10101], t);
    // t=i_101010=i_10101<<1
    ecp_sm2z256_ord_sqr_mont(t, table[i_10101], 1);
    // t=x6=i_101010+i_10101
    ecp_sm2z256_ord_mul_mont(t, t, table[i_10101]);
    // out=x8=x6<<2+i_11
    ecp_sm2z256_ord_sqr_mont(out, t, 2);
    ecp_sm2z256_ord_mul_mont(out, out, table[i_11]);
    // i_x31=x16=x8<<8+x8
    ecp_sm2z256_ord_sqr_mont(table[i_x31], out, 8);
    ecp_sm2z256_ord_mul_mont(table[i_x31], table[i_x31], out);
    // i_x32=x24=x16<<8+x8
    ecp_sm2z256_ord_sqr_mont(table[i_x32], table[i_x31], 8);
    ecp_sm2z256_ord_mul_mont(table[i_x32], table[i_x32], out);
    // out=x30=x24<<6+x6
    ecp_sm2z256_ord_sqr_mont(out, table[i_x32], 6);
    ecp_sm2z256_ord_mul_mont(out, out, t);
    // i_x31=x30<<1+i_1
    ecp_sm2z256_ord_sqr_mont(table[i_x31], out, 1);
    ecp_sm2z256_ord_mul_mont(table[i_x31], table[i_x31], table[i_1]);
    // i_x32=i_x31<<1+i_1
    ecp_sm2z256_ord_sqr_mont(table[i_x32], table[i_x31], 1);
    ecp_sm2z256_ord_mul_mont(table[i_x32], table[i_x32], table[i_1]);

    /* calculations */
    ecp_sm2z256_ord_sqr_mont(out, table[i_x31], 33);
    ecp_sm2z256_ord_mul_mont(out, out, table[i_x32]);

    for (i = 0; i < 25; i++) {
        static const struct { unsigned char p, i; } chain[25] = {
            { 32, i_x32 }, { 32, i_x32    }, { 4,  i_111    },
            { 3,  i_1   }, { 11, i_1111   }, { 5,  i_1111   },
            { 4,  i_1011}, { 5,  i_1011   }, { 3,  i_1      },
            { 7,  i_111 }, { 5,  i_11     }, { 9,  i_101    },
            { 7,  i_10101},{ 5,  i_10101  }, { 5,  i_111    },
            { 4,  i_111 }, { 6,  i_11111  }, { 3,  i_101    },
            { 10, i_1001}, { 5,  i_111    }, { 5,  i_111    },
            { 6,  i_10101},{ 2,  i_1      }, { 9,  i_1001   },
            { 5,  i_1   }
        };

        ecp_sm2z256_ord_sqr_mont(out, out, chain[i].p);
        ecp_sm2z256_ord_mul_mont(out, out, table[chain[i].i]);
    }
#endif
    // trans to normal field
    ecp_sm2z256_ord_mul_mont(out, out, one);

    /*
     * Can't fail, but check return code to be consistent anyway.
     */
    if (!bn_set_words(r, out, P256_LIMBS))
        goto err;

    ret = 1;
err:
    return ret;
}
#else
# define ecp_sm2z256_inv_mod_ord NULL
#endif

const EC_METHOD *EC_GFp_sm2z256_method(void)
{
    static const EC_METHOD ret = {
        EC_FLAGS_DEFAULT_OCT,
        NID_X9_62_prime_field,
        ossl_ec_GFp_mont_group_init,
        ossl_ec_GFp_mont_group_finish,
        ossl_ec_GFp_mont_group_clear_finish,
        ossl_ec_GFp_mont_group_copy,
        ossl_ec_GFp_mont_group_set_curve,
        ossl_ec_GFp_simple_group_get_curve,
        ossl_ec_GFp_simple_group_get_degree,
        ossl_ec_group_simple_order_bits,
        ossl_ec_GFp_simple_group_check_discriminant,
        ossl_ec_GFp_simple_point_init,
        ossl_ec_GFp_simple_point_finish,
        ossl_ec_GFp_simple_point_clear_finish,
        ossl_ec_GFp_simple_point_copy,
        ossl_ec_GFp_simple_point_set_to_infinity,
        ossl_ec_GFp_simple_point_set_affine_coordinates,
        ecp_sm2z256_get_affine,
        0, 0, 0,
        ossl_ec_GFp_simple_add,
        ossl_ec_GFp_simple_dbl,
        ossl_ec_GFp_simple_invert,
        ossl_ec_GFp_simple_is_at_infinity,
        ossl_ec_GFp_simple_is_on_curve,
        ossl_ec_GFp_simple_cmp,
        ossl_ec_GFp_simple_make_affine,
        ossl_ec_GFp_simple_points_make_affine,
        ecp_sm2z256_points_mul,                    /* mul */
        ecp_sm2z256_mult_precompute,               /* precompute_mult */
        ecp_sm2z256_window_have_precompute_mult,   /* have_precompute_mult */
        ossl_ec_GFp_mont_field_mul,
        ossl_ec_GFp_mont_field_sqr,
        0,                                          /* field_div */
        ossl_ec_GFp_mont_field_inv,
        ossl_ec_GFp_mont_field_encode,
        ossl_ec_GFp_mont_field_decode,
        ossl_ec_GFp_mont_field_set_to_one,
        ossl_ec_key_simple_priv2oct,
        ossl_ec_key_simple_oct2priv,
        0, /* set private */
        ossl_ec_key_simple_generate_key,
        ossl_ec_key_simple_check_key,
        ossl_ec_key_simple_generate_public_key,
        0, /* keycopy */
        0, /* keyfinish */
        ossl_ecdh_simple_compute_key,
        ossl_ecdsa_simple_sign_setup,
        ossl_ecdsa_simple_sign_sig,
        ossl_ecdsa_simple_verify_sig,
        ecp_sm2z256_inv_mod_ord,                    /* can be #define-d NULL */
        0,                                          /* blind_coordinates */
        0,                                          /* ladder_pre */
        0,                                          /* ladder_step */
        0                                           /* ladder_post */
    };

    return &ret;
}
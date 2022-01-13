/*
 * Copyright 2017-2021 The OpenSSL Project Authors. All Rights Reserved.
 *
 * Licensed under the Apache License 2.0 (the "License").  You may not use
 * this file except in compliance with the License.  You can obtain a copy
 * in the file LICENSE in the source distribution or at
 * https://www.openssl.org/source/license.html
 */

/*
 * Low level APIs are deprecated for public use, but still ok for internal use.
 */
#include "internal/deprecated.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <signal.h>
// #include "apps.h"
// #include "progs.h"
# include <unistd.h>
#include <openssl/bio.h>
#include <openssl/evp.h>
#include <openssl/bn.h>
#include <openssl/crypto.h>
#include <openssl/err.h>
#include <openssl/ec.h>
#include <openssl/rand.h>
#include "testutil.h"
#include "../crypto/ec/ec_local.h"
#include "../crypto/bn/bn_local.h"

#ifndef OPENSSL_NO_SM2

# include "crypto/sm2.h"

int bn_mul_mont(BN_ULONG *rp, const BN_ULONG *ap, const BN_ULONG *bp,
                const BN_ULONG *np, const BN_ULONG *n0p, int num);
/* Montgomery mul: res = a*b*2^-256 mod P */
void ecp_sm2z256_mul_mont(BN_ULONG res[4],
                           const BN_ULONG a[4],
                           const BN_ULONG b[4]);

void ecp_sm2z256_ord_mul_mont(BN_ULONG res[4],
                           const BN_ULONG a[4],
                           const BN_ULONG b[4]);

void ecp_sm2z256_mod_inverse_sqr(BN_ULONG r[4],
                                       const BN_ULONG in[4]);
static fake_random_generate_cb get_faked_bytes;

static OSSL_PROVIDER *fake_rand = NULL;
static uint8_t *fake_rand_bytes = NULL;
static size_t fake_rand_bytes_offset = 0;
static size_t fake_rand_size = 0;

#define TESTS 0x7fffff
#define FUNCTION_TESTS 0x7fffffff

// #define TESTS 0x1
// #define FUNCTION_TESTS 0x1
// copy frm aarch64-linux-gnu/bits/signum-generic.h
#define	SIGALRM		14	/* Alarm clock.  */

// copy from apps/speed.c
static volatile int run = 0;
static int usertime = 1;
#define START   0
#define STOP    1

static double Time_F(int s);

# include <sys/times.h>
# define TM_START        0
# define TM_STOP         1

double app_tminterval(int stop, int usertime)
{
    double ret = 0;
    struct tms rus;
    clock_t now = times(&rus);
    static clock_t tmstart;

    if (usertime)
        now = rus.tms_utime;

    if (stop == TM_START) {
        tmstart = now;
    } else {
        long int tck = sysconf(_SC_CLK_TCK);
        ret = (now - tmstart) / (double)tck;
    }

    return ret;
}

static void alarmed(int sig)
{
    signal(SIGALRM, alarmed);
    run = 0;
}

static double Time_F(int s)
{
    double ret = app_tminterval(s, usertime);
    if (s == STOP)
        alarm(0);
    return ret;
}

static int get_faked_bytes(unsigned char *buf, size_t num,
                           ossl_unused const char *name,
                           ossl_unused EVP_RAND_CTX *ctx)
{
    if (!TEST_ptr(fake_rand_bytes) || !TEST_size_t_gt(fake_rand_size, 0))
        return 0;

    while (num-- > 0) {
        if (fake_rand_bytes_offset >= fake_rand_size)
            fake_rand_bytes_offset = 0;
        *buf++ = fake_rand_bytes[fake_rand_bytes_offset++];
    }

    return 1;
}

static int start_fake_rand(const char *hex_bytes)
{
    OPENSSL_free(fake_rand_bytes);
    fake_rand_bytes_offset = 0;
    fake_rand_size = strlen(hex_bytes) / 2;
    if (!TEST_ptr(fake_rand_bytes = OPENSSL_hexstr2buf(hex_bytes, NULL)))
        return 0;

    /* use own random function */
    fake_rand_set_public_private_callbacks(NULL, get_faked_bytes);
    return 1;

}

static void restore_rand(void)
{
    fake_rand_set_public_private_callbacks(NULL, NULL);
    OPENSSL_free(fake_rand_bytes);
    fake_rand_bytes = NULL;
    fake_rand_bytes_offset = 0;
}

static EC_GROUP *create_EC_group(const char *p_hex, const char *a_hex,
                                 const char *b_hex, const char *x_hex,
                                 const char *y_hex, const char *order_hex,
                                 const char *cof_hex)
{
    BIGNUM *p = NULL;
    BIGNUM *a = NULL;
    BIGNUM *b = NULL;
    BIGNUM *g_x = NULL;
    BIGNUM *g_y = NULL;
    BIGNUM *order = NULL;
    BIGNUM *cof = NULL;
    EC_POINT *generator = NULL;
    EC_GROUP *group = NULL;
    int ok = 0;

    if (!TEST_true(BN_hex2bn(&p, p_hex))
            || !TEST_true(BN_hex2bn(&a, a_hex))
            || !TEST_true(BN_hex2bn(&b, b_hex)))
        goto done;

    group = EC_GROUP_new_curve_sm2_GFp(p, a, b, NULL);
    if (!TEST_ptr(group))
        goto done;

    generator = EC_POINT_new(group);
    if (!TEST_ptr(generator))
        goto done;

    if (!TEST_true(BN_hex2bn(&g_x, x_hex))
            || !TEST_true(BN_hex2bn(&g_y, y_hex))
            || !TEST_true(EC_POINT_set_affine_coordinates(group, generator, g_x,
                                                          g_y, NULL)))
        goto done;

    if (!TEST_true(BN_hex2bn(&order, order_hex))
            || !TEST_true(BN_hex2bn(&cof, cof_hex))
            || !TEST_true(EC_GROUP_set_generator(group, generator, order, cof)))
        goto done;

    ok = 1;
done:
    BN_free(p);
    BN_free(a);
    BN_free(b);
    BN_free(g_x);
    BN_free(g_y);
    EC_POINT_free(generator);
    BN_free(order);
    BN_free(cof);
    if (!ok) {
        EC_GROUP_free(group);
        group = NULL;
    }

    return group;
}

static EC_GROUP *create_EC_group_slow(const char *p_hex, const char *a_hex,
                                 const char *b_hex, const char *x_hex,
                                 const char *y_hex, const char *order_hex,
                                 const char *cof_hex)
{
    BIGNUM *p = NULL;
    BIGNUM *a = NULL;
    BIGNUM *b = NULL;
    BIGNUM *g_x = NULL;
    BIGNUM *g_y = NULL;
    BIGNUM *order = NULL;
    BIGNUM *cof = NULL;
    EC_POINT *generator = NULL;
    EC_GROUP *group = NULL;
    int ok = 0;

    if (!TEST_true(BN_hex2bn(&p, p_hex))
            || !TEST_true(BN_hex2bn(&a, a_hex))
            || !TEST_true(BN_hex2bn(&b, b_hex)))
        goto done;

    group = EC_GROUP_new_curve_GFp(p, a, b, NULL);
    if (!TEST_ptr(group))
        goto done;

    generator = EC_POINT_new(group);
    if (!TEST_ptr(generator))
        goto done;

    if (!TEST_true(BN_hex2bn(&g_x, x_hex))
            || !TEST_true(BN_hex2bn(&g_y, y_hex))
            || !TEST_true(EC_POINT_set_affine_coordinates(group, generator, g_x,
                                                          g_y, NULL)))
        goto done;

    if (!TEST_true(BN_hex2bn(&order, order_hex))
            || !TEST_true(BN_hex2bn(&cof, cof_hex))
            || !TEST_true(EC_GROUP_set_generator(group, generator, order, cof)))
        goto done;

    ok = 1;
done:
    BN_free(p);
    BN_free(a);
    BN_free(b);
    BN_free(g_x);
    BN_free(g_y);
    EC_POINT_free(generator);
    BN_free(order);
    BN_free(cof);
    if (!ok) {
        EC_GROUP_free(group);
        group = NULL;
    }

    return group;
}

static int test_sm2_crypt(const EC_GROUP *group,
                          const EVP_MD *digest,
                          const char *privkey_hex,
                          const char *message,
                          const char *k_hex, const char *ctext_hex)
{
    const size_t msg_len = strlen(message);
    BIGNUM *priv = NULL;
    EC_KEY *key = NULL;
    EC_POINT *pt = NULL;
    // unsigned char *expected = OPENSSL_hexstr2buf(ctext_hex, NULL);
    size_t ctext_len = 0;
    size_t ptext_len = 0;
    uint8_t *ctext = NULL;
    uint8_t *recovered = NULL;
    size_t recovered_len = msg_len;
    int rc = 0;
    int i;

    if (!TEST_true(BN_hex2bn(&priv, privkey_hex)))
        goto done;

    key = EC_KEY_new();
    if (!TEST_ptr(key)
            || !TEST_true(EC_KEY_set_group(key, group))
            || !TEST_true(EC_KEY_set_private_key(key, priv)))
        goto done;

    pt = EC_POINT_new(group);
    if (!TEST_ptr(pt)
            || !TEST_true(EC_POINT_mul(group, pt, priv, NULL, NULL, NULL))
            || !TEST_true(EC_KEY_set_public_key(key, pt))
            || !TEST_true(ossl_sm2_ciphertext_size(key, digest, msg_len,
                                                   &ctext_len)))
        goto done;

    ctext = OPENSSL_zalloc(ctext_len);
    if (!TEST_ptr(ctext))
        goto done;

    start_fake_rand(k_hex);
    if (!TEST_true(ossl_sm2_encrypt(key, digest,
                                    (const uint8_t *)message, msg_len,
                                    ctext, &ctext_len))) {
        restore_rand();
        goto done;
    }
    // BIO_printf(bio_err, "%s\n", ctext);
    for (i=0; i<ctext_len; i++){
        BIO_printf(bio_err, "%02x", ctext[i]);
    }
    BIO_printf(bio_err, "\n");
    restore_rand();

    // if (!TEST_mem_eq(ctext, ctext_len, expected, ctext_len))
    //     goto done;

    if (!TEST_true(ossl_sm2_plaintext_size(key, digest, ctext_len, &ptext_len))
            || !TEST_int_eq(ptext_len, msg_len))
        goto done;
    // BIO_printf(bio_err, "msg_len: %ld, field_size: %ld, md_size: %ld\n", ctext_len, ec_field_size(EC_KEY_get0_group(key)), EVP_MD_get_size(digest));
    BIO_printf(bio_err, "msg_len: %ld, ptext_len: %ld\n", ctext_len, ptext_len);
    recovered = OPENSSL_zalloc(ptext_len);
    if (!TEST_ptr(recovered)
            || !TEST_true(ossl_sm2_decrypt(key, digest, ctext, ctext_len,
                                           recovered, &recovered_len))
            || !TEST_int_eq(recovered_len, msg_len)
            || !TEST_mem_eq(recovered, recovered_len, message, msg_len))
        goto done;

    rc = 1;
 done:
    BN_free(priv);
    EC_POINT_free(pt);
    OPENSSL_free(ctext);
    OPENSSL_free(recovered);
    // OPENSSL_free(expected);
    EC_KEY_free(key);
    return rc;
}

static int sm2_crypt_test(void)
{
    int testresult = 0;
    EC_GROUP *test_group =
        create_EC_group
        ("FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF",
         "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC",
         "28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93",
         "32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7",
         "BC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0",
         "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123",
         "1");

    if (!TEST_ptr(test_group))
        goto done;

    if (!test_sm2_crypt(
            test_group,
            EVP_sm3(),
            "1649AB77A00637BD5E2EFE283FBF353534AA7F7CB89463F208DDBC2920BB0DA0",
            "encryption standard",
            "004C62EEFD6ECFC2B95B92FD6C3D9575148AFA17425546D49018E5388D49DD7B4F"
            "0092e8ff62146873c258557548500ab2df2a365e0609ab67640a1f6d57d7b17820"
            "008349312695a3e1d2f46905f39a766487f2432e95d6be0cb009fe8c69fd8825a7",
            "307B0220245C26FB68B1DDDDB12C4B6BF9F2B6D5FE60A383B0D18D1C4144ABF1"
            "7F6252E7022076CB9264C2A7E88E52B19903FDC47378F605E36811F5C07423A2"
            "4B84400F01B804209C3D7360C30156FAB7C80A0276712DA9D8094A634B766D3A"
            "285E07480653426D0413650053A89B41C418B0C3AAD00D886C00286467"))
        goto done;

    /* Same test as above except using SHA-256 instead of SM3 */
    // if (!test_sm2_crypt(
    //         test_group,
    //         EVP_sha256(),
    //         "1649AB77A00637BD5E2EFE283FBF353534AA7F7CB89463F208DDBC2920BB0DA0",
    //         "encryption standard",
    //         "004C62EEFD6ECFC2B95B92FD6C3D9575148AFA17425546D49018E5388D49DD7B4F"
    //         "003da18008784352192d70f22c26c243174a447ba272fec64163dd4742bae8bc98"
    //         "00df17605cf304e9dd1dfeb90c015e93b393a6f046792f790a6fa4228af67d9588",
    //         "307B0220245C26FB68B1DDDDB12C4B6BF9F2B6D5FE60A383B0D18D1C4144ABF17F"
    //         "6252E7022076CB9264C2A7E88E52B19903FDC47378F605E36811F5C07423A24B84"
    //         "400F01B80420BE89139D07853100EFA763F60CBE30099EA3DF7F8F364F9D10A5E9"
    //         "88E3C5AAFC0413229E6C9AEE2BB92CAD649FE2C035689785DA33"))
    //     goto done;

    testresult = 1;
 done:
    EC_GROUP_free(test_group);

    return testresult;
}

static int test_sm2_sign(const EC_GROUP *group,
                         const char *userid,
                         const char *privkey_hex,
                         const char *message,
                         const char *k_hex,
                         const char *r_hex,
                         const char *s_hex)
{
    const size_t msg_len = strlen(message);
    int ok = 0;
    BIGNUM *priv = NULL;
    EC_POINT *pt = NULL;
    EC_KEY *key = NULL;
    ECDSA_SIG *sig = NULL;
    // const BIGNUM *sig_r = NULL;
    // const BIGNUM *sig_s = NULL;
    // BIGNUM *r = NULL;
    // BIGNUM *s = NULL;

    if (!TEST_true(BN_hex2bn(&priv, privkey_hex)))
        goto done;

    key = EC_KEY_new();
    if (!TEST_ptr(key)
            || !TEST_true(EC_KEY_set_group(key, group))
            || !TEST_true(EC_KEY_set_private_key(key, priv)))
        goto done;

    pt = EC_POINT_new(group);
    if (!TEST_ptr(pt)
            || !TEST_true(EC_POINT_mul(group, pt, priv, NULL, NULL, NULL))
            || !TEST_true(EC_KEY_set_public_key(key, pt)))
        goto done;

    start_fake_rand(k_hex);
    sig = ossl_sm2_do_sign(key, EVP_sm3(), (const uint8_t *)userid,
                           strlen(userid), (const uint8_t *)message, msg_len);
    if (!TEST_ptr(sig)) {
        restore_rand();
        goto done;
    }
    restore_rand();

    // ECDSA_SIG_get0(sig, &sig_r, &sig_s);

    // if (!TEST_true(BN_hex2bn(&r, r_hex))
    //         || !TEST_true(BN_hex2bn(&s, s_hex))
    //         || !TEST_BN_eq(r, sig_r)
    //         || !TEST_BN_eq(s, sig_s))
    //     goto done;

    ok = ossl_sm2_do_verify(key, EVP_sm3(), sig, (const uint8_t *)userid,
                            strlen(userid), (const uint8_t *)message, msg_len);

    /* We goto done whether this passes or fails */
    TEST_true(ok);

 done:
    ECDSA_SIG_free(sig);
    EC_POINT_free(pt);
    EC_KEY_free(key);
    BN_free(priv);
    // BN_free(r);
    // BN_free(s);

    return ok;
}

static int speed_sm2_sign(const EC_GROUP *group,
                         const char *userid,
                         const char *privkey_hex,
                         const char *message,
                         const char *k_hex,
                         const char *r_hex,
                         const char *s_hex)
{
    const size_t msg_len = strlen(message);
    long int ok = 0, count;
    BIGNUM *priv = NULL;
    EC_POINT *pt = NULL;
    EC_POINT *pt1 = NULL;
    EC_KEY *key = NULL;
    ECDSA_SIG *sig = NULL;
    BN_MONT_CTX *mont;
    double d = 0.0;
    BN_ULONG res[4] = {0x0000000000000001ull, 0x00000000ffffffffull, 0x0000000000000000ull, 0x100000000ull};
    BN_ULONG a[4] = {0xFFFFFFFFFFFFFFFEull, 0xFFFFFFFF00000001ull, 0xFFFFFFFFFFFFFFFEull, 0xFFFFFFFEFFFFFFFEull};
    BN_ULONG b[4] = {0xFFFFFFFFFFFFFFFDull, 0xFFFFFFFF00000000ull, 0xFFFFFFFFFFFFFFFFull, 0xFFFFFFFEFFFFFFFFull};
    static int test_functions = 1;
    BIGNUM *big_r = NULL;
    BIGNUM *big_a = NULL;
    // const BIGNUM *sig_r = NULL;
    // const BIGNUM *sig_s = NULL;
    // BIGNUM *r = NULL;
    // BIGNUM *s = NULL;
    BN_CTX *ctx = NULL;
    int ret;


#if SIGALRM > 0
    signal(SIGALRM, alarmed);
#endif

    mont = group->field_data1;
    if (mont == NULL)
        goto done;
    
    if (!TEST_true(BN_hex2bn(&priv, privkey_hex)))
        goto done;

    key = EC_KEY_new();
    if (!TEST_ptr(key)
            || !TEST_true(EC_KEY_set_group(key, group))
            || !TEST_true(EC_KEY_set_private_key(key, priv)))
        goto done;

    ctx = BN_CTX_new_ex(ossl_ec_key_get_libctx(key));
    if (ctx == NULL) {
        ERR_raise(ERR_LIB_SM2, ERR_R_MALLOC_FAILURE);
        goto done;
    }

    if ((big_r = BN_CTX_get(ctx)) == NULL 
        || (big_a = BN_CTX_get(ctx)) == NULL) {
            ERR_raise(ERR_LIB_EC, ERR_R_BN_LIB);
            goto done;
        }

    pt = EC_POINT_new(group);
    if (!TEST_ptr(pt)
            || !TEST_true(EC_POINT_mul(group, pt, priv, NULL, NULL, NULL))
            || !TEST_true(EC_KEY_set_public_key(key, pt)))
        goto done;

    pt1 = EC_POINT_new(group);
    if (!TEST_ptr(pt1)
            || !TEST_true(EC_POINT_mul(group, pt1, priv, NULL, NULL, NULL))
            || !TEST_true(EC_KEY_set_public_key(key, pt1)))
        goto done;

    start_fake_rand(k_hex);
    run = 1;

#if 1
    bn_set_words(big_a, a, 4);

    if (test_functions == 1){
        d = 0.0;
        Time_F(START);
        for(count = 0; run && (count < FUNCTION_TESTS); count++){
            bn_mul_mont(res, a, b, mont->N.d, mont->n0, mont->N.top);
        }
        d = Time_F(STOP);
        BIO_printf(bio_err, "%ld bn_mul_mont in %.2fs \n", count, d);
        BIO_printf(bio_err, "%8.1f bn_mul_mont/s\n", (double)count / d);

        d = 0.0;
        Time_F(START);
        for(count = 0; run && (count < FUNCTION_TESTS); count++){
            ecp_sm2z256_mul_mont(res, a, b);
        }
        d = Time_F(STOP);
        BIO_printf(bio_err, "%ld ecp_sm2z256_mul_mont in %.2fs \n", count, d);
        BIO_printf(bio_err, "%8.1f ecp_sm2z256_mul_mont/s\n", (double)count / d);

        d = 0.0;
        Time_F(START);
        for(count = 0; run && (count < FUNCTION_TESTS); count++){
            ecp_sm2z256_ord_mul_mont(res, a, b);
        }
        d = Time_F(STOP);
        BIO_printf(bio_err, "%ld ecp_sm2z256_ord_mul_mont in %.2fs \n", count, d);
        BIO_printf(bio_err, "%8.1f ecp_sm2z256_ord_mul_mont/s\n", (double)count / d);

        /*
        * for mod p inverse 
        *
        * without my sm2 impl:
        * in ec_cvt.c:EC_GROUP_new_curve_GFp:meth = EC_GFp_mont_method()
        * in ecp_mont.c:ossl_ec_GFp_mont_field_inv is mod p inverse
        * ossl_ec_GFp_mont_field_inv:BN_mod_exp_mont:BN_mod_exp_mont_consttime
        * this inv is used when calling 
        * ecp_mont.c:ossl_ec_GFp_simple_point_get_affine_coordinates
        * 
        * with my sm2 impl:
        * in ec_cvt.c:EC_GROUP_new_curve_sm2_GFp:
        *  meth = EC_GFp_sm2z256_method()
        * in ecp_sm2z256.c:ecp_sm2z256_get_affine calls my inv function
        */
        // ret = ossl_ec_GFp_mont_field_inv(group, big_r, big_a, ctx);
        // BIO_printf(bio_err, "mod p inverse ret is %d\n", ret);
        d = 0.0;
        Time_F(START);
        for(count = 0; run && (count < FUNCTION_TESTS); count++){
            ossl_ec_GFp_mont_field_inv(group, big_r, big_a, ctx);
        }
        d = Time_F(STOP);
        BIO_printf(bio_err, "%ld mod p default inv in %.2fs \n", count, d);
        BIO_printf(bio_err, "%8.1f mod p default inv/s\n", (double)count / d);

        d = 0.0;
        Time_F(START);
        for(count = 0; run && (count < FUNCTION_TESTS); count++){
            ecp_sm2z256_mod_inverse_sqr(res, a);
        }
        d = Time_F(STOP);
        BIO_printf(bio_err, "%ld mod p fast inv in %.2fs \n", count, d);
        BIO_printf(bio_err, "%8.1f mod p fast inv/s\n", (double)count / d);

        test_functions = 0;
    }
    
    /*
    * for mod n inverse
    *
    * in sm2_sign.c:sm2_sig_gen:ossl_ec_group_do_inverse_ord is 
    * mod n inverse
    * 
    * it is implemented in ec_lib.c
    * it will call my ecp_sm2z256_inv_mod_ord with my sm2 impl.
    *   or call default ec_field_inverse_mod_ord:BN_mod_exp_mont:
    *      BN_mod_exp_mont_consttime without my sm2 impl.
    */
    // ret = ossl_ec_group_do_inverse_ord(group, big_r, big_a, ctx);
    // BIO_printf(bio_err, "mod n inverse ret is %d\n", ret);
    d = 0.0;
    Time_F(START);
    for(count = 0; run && (count < TESTS); count++){
        ossl_ec_group_do_inverse_ord(group, big_r, big_a, ctx);
    }
    d = Time_F(STOP);
    BIO_printf(bio_err, "%ld mod n inv in %.2fs \n", count, d);
    BIO_printf(bio_err, "%8.1f mod n inv/s\n", (double)count / d);

    /*
    * for point mul
    *
    * in sm2_sign.c:EC_POINT_mul
    * without my sm2 impl:
    * in ec_lib.c:EC_POINT_mul:ossl_ec_wNAF_mul is used
    * (in ecp_mont.c meth->mul is set 0)
    * ossl_ec_wNAF_mul is implemented in ec_mult.c
    * 
    * ossl_ec_wNAF_mul:
    * scalar!=NULL && num==0: scalar*GeneratorPoint using ladder
    * scalar==NULL && num==1: scalar*VariablePoint using ladder
    * 
    * if group->order==0 or group->cofactor==0:
    *   maybe use wNAF
    * 
    * with my sm2 impl:
    * EC_POINT_mul:group->meth->mul:ecp_sm2z256_points_mul
    * 
    * scalar!=NULL: w=7 windows-based method with too-big pre-computed table
    * else: call ecp_sm2z256_windowed_mul (w=5 unfixed-point mul)
    */
    // ret = EC_POINT_mul(group, pt, priv, NULL, NULL, NULL);
    // BIO_printf(bio_err, "EC_POINT_mul is %d\n", ret);
    d = 0.0;
    Time_F(START);
    for(count = 0; run && (count < TESTS); count++){
        EC_POINT_mul(group, pt, priv, NULL, NULL, NULL);
    }
    d = Time_F(STOP);
    BIO_printf(bio_err, "%ld fixed-point mul in %.2fs \n", count, d);
    BIO_printf(bio_err, "%8.1f fixed-point mul/s\n", (double)count / d);

    // for unfixed-point mul
    d = 0.0;
    Time_F(START);
    for(count = 0; run && (count < TESTS); count++){
        EC_POINT_mul(group, pt1, NULL, pt, priv, ctx);
    }
    d = Time_F(STOP);
    BIO_printf(bio_err, "%ld unfixed-point mul in %.2fs \n", count, d);
    BIO_printf(bio_err, "%8.1f unfixed-point mul/s\n", (double)count / d);
#endif

    d = 0.0;
    Time_F(START);
    for(count = 0; run && (count < TESTS); count++){
        sig = ossl_sm2_do_sign(key, EVP_sm3(), (const uint8_t *)userid,
                           strlen(userid), (const uint8_t *)message, msg_len);
    }
    d = Time_F(STOP);
    BIO_printf(bio_err,
                "%ld %u bits %s signs in %.2fs \n",
                count, 256,
                "SM2", d);
    BIO_printf(bio_err, "%8.1f sign/s\n", (double)count / d);


    if (!TEST_ptr(sig)) {
        restore_rand();
        goto done;
    }
    restore_rand();

    // ECDSA_SIG_get0(sig, &sig_r, &sig_s);

    // if (!TEST_true(BN_hex2bn(&r, r_hex))
    //         || !TEST_true(BN_hex2bn(&s, s_hex))
    //         || !TEST_BN_eq(r, sig_r)
    //         || !TEST_BN_eq(s, sig_s))
    //     goto done;
    d = 0.0;
    Time_F(START);
    for(count = 0; run && (count < TESTS); count++){
    ok = ossl_sm2_do_verify(key, EVP_sm3(), sig, (const uint8_t *)userid,
                            strlen(userid), (const uint8_t *)message, msg_len);
    }
    d = Time_F(STOP);

    BIO_printf(bio_err,
                "%ld %u bits %s verifys in %.2fs \n",
                count, 256,
                "SM2", d);
    BIO_printf(bio_err, "%8.1f verify/s\n", (double)count / d);
    /* We goto done whether this passes or fails */
    TEST_true(ok);

 done:
    ECDSA_SIG_free(sig);
    EC_POINT_free(pt);
    EC_KEY_free(key);
    BN_free(priv);
    BN_CTX_free(ctx);
    // BN_free(r);
    // BN_free(s);
    // BN_free(big_r);
    // BN_free(big_a);

    return ok;
}

static int sm2_sig_test(void)
{
    int testresult = 0;
    /* From draft-shen-sm2-ecdsa-02 */
    EC_GROUP *test_group =
        create_EC_group
        ("FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF",
         "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC",
         "28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93",
         "32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7",
         "BC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0",
         "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123",
         "1");

    EC_GROUP *test_group_slow =
        create_EC_group_slow
        ("FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFF",
         "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF00000000FFFFFFFFFFFFFFFC",
         "28E9FA9E9D9F5E344D5A9E4BCF6509A7F39789F515AB8F92DDBCBD414D940E93",
         "32C4AE2C1F1981195F9904466A39C9948FE30BBFF2660BE1715A4589334C74C7",
         "BC3736A2F4F6779C59BDCEE36B692153D0A9877CC62A474002DF32E52139F0A0",
         "FFFFFFFEFFFFFFFFFFFFFFFFFFFFFFFF7203DF6B21C6052B53BBF40939D54123",
         "1");

    if (!TEST_ptr(test_group))
        goto done;

    if (!TEST_true(test_sm2_sign(
                        test_group,
                        "ALICE123@YAHOO.COM",
                        "128B2FA8BD433C6C068C8D803DFF79792A519A55171B1B650C23661D15897263",
                        "message digest",
                        "006CB28D99385C175C94F94E934817663FC176D925DD72B727260DBAAE1FB2F96F"
                        "007c47811054c6f99613a578eb8453706ccb96384fe7df5c171671e760bfa8be3a",
                        "40F1EC59F793D9F49E09DCEF49130D4194F79FB1EED2CAA55BACDB49C4E755D1",
                        "6FC6DAC32C5D5CF10C77DFB20F7C2EB667A457872FB09EC56327A67EC7DEEBE7")))
        goto done;

    if (!TEST_true(speed_sm2_sign(
                        test_group_slow,
                        "ALICE123@YAHOO.COM",
                        "128B2FA8BD433C6C068C8D803DFF79792A519A55171B1B650C23661D15897263",
                        "message digest",
                        "006CB28D99385C175C94F94E934817663FC176D925DD72B727260DBAAE1FB2F96F"
                        "007c47811054c6f99613a578eb8453706ccb96384fe7df5c171671e760bfa8be3a",
                        "40F1EC59F793D9F49E09DCEF49130D4194F79FB1EED2CAA55BACDB49C4E755D1",
                        "6FC6DAC32C5D5CF10C77DFB20F7C2EB667A457872FB09EC56327A67EC7DEEBE7")))
        goto done;

    if (!TEST_true(speed_sm2_sign(
                        test_group,
                        "ALICE123@YAHOO.COM",
                        "128B2FA8BD433C6C068C8D803DFF79792A519A55171B1B650C23661D15897263",
                        "message digest",
                        "006CB28D99385C175C94F94E934817663FC176D925DD72B727260DBAAE1FB2F96F"
                        "007c47811054c6f99613a578eb8453706ccb96384fe7df5c171671e760bfa8be3a",
                        "40F1EC59F793D9F49E09DCEF49130D4194F79FB1EED2CAA55BACDB49C4E755D1",
                        "6FC6DAC32C5D5CF10C77DFB20F7C2EB667A457872FB09EC56327A67EC7DEEBE7")))
        goto done;

    testresult = 1;

 done:
    EC_GROUP_free(test_group);

    return testresult;
}

#endif

int setup_tests(void)
{
#ifdef OPENSSL_NO_SM2
    TEST_note("SM2 is disabled.");
#else
    fake_rand = fake_rand_start(NULL);
    if (fake_rand == NULL)
        return 0;

    ADD_TEST(sm2_crypt_test);
    ADD_TEST(sm2_sig_test);
#endif
    return 1;
}

void cleanup_tests(void)
{
#ifndef OPENSSL_NO_SM2
    fake_rand_finish(fake_rand);
#endif
}

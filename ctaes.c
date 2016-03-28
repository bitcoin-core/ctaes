 /*********************************************************************
 * Copyright (c) 2016 Pieter Wuille                                   *
 * Distributed under the MIT software license, see the accompanying   *
 * file COPYING or http://www.opensource.org/licenses/mit-license.php.*
 **********************************************************************/

/* Constant time, unoptimized, concise, plain C, AES implementation
 * Based On:
 *   Emilia Kasper and Peter Schwabe, Faster and Timing-Attack Resistant AES-GCM
 *   http://www.iacr.org/archive/ches2009/57470001/57470001.pdf
 * But using 8 16-bit integers representing a single AES state rather than 8 128-bit
 * integers representing 8 AES states.
 */

#include "ctaes.h"

/* Slice variable slice_i contains the i'th bit of the 16 state variables in this order:
 *  0  1  2  3
 *  4  5  6  7
 *  8  9 10 11
 * 12 13 14 15
 */

/** Load 4 32-bit MSB words representing columns of data into 8 sliced integers */
static void LoadWords(AES_state* s, uint32_t w0, uint32_t w1, uint32_t w2, uint32_t w3) {
    int b, c;
    for (b = 0; b < 8; b++) {
        s->slice[b] = 0;
    }
    for (c = 0; c < 4; c++) {
        int r;
        uint32_t w = c & 2 ? (c & 1 ? w3 : w2) : (c & 1 ? w1 : w0);
        for (r = 0; r < 4; r++) {
            int i;
            uint8_t v = w >> 24;
            w <<= 8;
            for (i = 0; i < 8; i++) {
                s->slice[i] |= (v & 1) << (r * 4 + c);
                v >>= 1;
            }
        }
    }
}

/** Load 16 bytes of data into 8 sliced integers */
static void LoadBytes(AES_state *s, const unsigned char* data16) {
    uint32_t w[4];
    int i;
    for (i = 0; i < 4; i++) {
        w[i] = ((uint32_t)data16[0]) << 24 | ((uint32_t)data16[1]) << 16 | ((uint32_t)data16[2]) << 8 | ((uint32_t)data16[3]);
        data16 += 4;
    }
    LoadWords(s, w[0], w[1], w[2], w[3]);
}

/** Convert 8 sliced integers into 16 bytes of data */
static void SaveBytes(unsigned char* data16, const AES_state *s) {
    int c;
    for (c = 0; c < 4; c++) {
        int r;
        for (r = 0; r < 4; r++) {
            int b;
            uint8_t v = 0;
            for (b = 0; b < 8; b++) {
                v |= ((s->slice[b] >> (r * 4 + c)) & 1) << b;
            }
            *(data16++) = v;
        }
    }
}

/* S-box implementation based on the gate logic from:
 *   Joan Boyar and Rene Peralta, A depth-16 circuit for the AES S-box.
 *   https://eprint.iacr.org/2011/332.pdf
*/
static void SubBytes(AES_state *s, int inv) {
    /* Load the bit slices */
    uint16_t U0 = s->slice[7], U1 = s->slice[6], U2 = s->slice[5], U3 = s->slice[4];
    uint16_t U4 = s->slice[3], U5 = s->slice[2], U6 = s->slice[1], U7 = s->slice[0];

    uint16_t T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, T12, T13, T14, T15, T16;
    uint16_t T17, T18, T19, T20, T21, T22, T23, T24, T25, T26, T27, D;

    if (inv) {
        /* Undo linear postprocessing */
        T23 = U0 ^ U3;
        T22 = ~(U1 ^ U3);
        T2 = ~(U0 ^ U1);
        T1 = U3 ^ U4;
        T24 = ~(U4 ^ U7);
        uint16_t R5 = U6 ^ U7;
        T8 = ~(U1 ^ T23);
        T19 = T22 ^ R5;
        T9 = ~(U7 ^ T1);
        T10 = T2 ^ T24;
        T13 = T2 ^ R5;
        T3 = T1 ^ R5;
        T25 = ~(U2 ^ T1);
        uint16_t R13 = U1 ^ U6;
        T17 = ~(U2 ^ T19);
        T20 = T24 ^ R13;
        T4 = U4 ^ T8;
        uint16_t R17 = ~(U2 ^ U5);
        uint16_t R18 = ~(U5 ^ U6);
        uint16_t R19 = ~(U2 ^ U4);
        D = U0 ^ R17;
        T6 = T22 ^ R17;
        T16 = R13 ^ R19;
        T27 = T1 ^ R18;
        T15 = T10 ^ T27;
        T14 = T10 ^ R18;
        T26 = T3 ^ T16;
    } else {
        /* Linear preprocessing. */
        T1 = U0 ^ U3;
        T2 = U0 ^ U5;
        T3 = U0 ^ U6;
        T4 = U3 ^ U5;
        T5 = U4 ^ U6;
        T6 = T1 ^ T5;
        T7 = U1 ^ U2;
        T8 = U7 ^ T6;
        T9 = U7 ^ T7;
        T10 = T6 ^ T7;
        T11 = U1 ^ U5;
        T12 = U2 ^ U5;
        T13 = T3 ^ T4;
        T14 = T6 ^ T11;
        T15 = T5 ^ T11;
        T16 = T5 ^ T12;
        T17 = T9 ^ T16;
        T18 = U3 ^ U7;
        T19 = T7 ^ T18;
        T20 = T1 ^ T19;
        T21 = U6 ^ U7;
        T22 = T7 ^ T21;
        T23 = T2 ^ T22;
        T24 = T2 ^ T10;
        T25 = T20 ^ T17;
        T26 = T3 ^ T16;
        T27 = T1 ^ T12;
        D = U7;
    }

    /* Non-linear transformation (identical to the code in SubBytes) */
    uint16_t M1 = T13 & T6;
    uint16_t M6 = T3 & T16;
    uint16_t M11 = T1 & T15;
    uint16_t M13 = (T4 & T27) ^ M11;
    uint16_t M15 = (T2 & T10) ^ M11;
    uint16_t M20 = T14 ^ M1 ^ (T23 & T8) ^ M13;
    uint16_t M21 = (T19 & D) ^ M1 ^ T24 ^ M15;
    uint16_t M22 = T26 ^ M6 ^ (T22 & T9) ^ M13;
    uint16_t M23 = (T20 & T17) ^ M6 ^ M15 ^ T25;
    uint16_t M25 = M22 & M20;
    uint16_t M37 = M21 ^ ((M20 ^ M21) & (M23 ^ M25));
    uint16_t M38 = M20 ^ M25 ^ (M21 | (M20 & M23));
    uint16_t M39 = M23 ^ ((M22 ^ M23) & (M21 ^ M25));
    uint16_t M40 = M22 ^ M25 ^ (M23 | (M21 & M22));
    uint16_t M41 = M38 ^ M40;
    uint16_t M42 = M37 ^ M39;
    uint16_t M43 = M37 ^ M38;
    uint16_t M44 = M39 ^ M40;
    uint16_t M45 = M42 ^ M41;
    uint16_t M46 = M44 & T6;
    uint16_t M47 = M40 & T8;
    uint16_t M48 = M39 & D;
    uint16_t M49 = M43 & T16;
    uint16_t M50 = M38 & T9;
    uint16_t M51 = M37 & T17;
    uint16_t M52 = M42 & T15;
    uint16_t M53 = M45 & T27;
    uint16_t M54 = M41 & T10;
    uint16_t M55 = M44 & T13;
    uint16_t M56 = M40 & T23;
    uint16_t M57 = M39 & T19;
    uint16_t M58 = M43 & T3;
    uint16_t M59 = M38 & T22;
    uint16_t M60 = M37 & T20;
    uint16_t M61 = M42 & T1;
    uint16_t M62 = M45 & T4;
    uint16_t M63 = M41 & T2;

    if (inv){
        /* Undo linear preprocessing */
        uint16_t P0 = M52 ^ M61;
        uint16_t P1 = M58 ^ M59;
        uint16_t P2 = M54 ^ M62;
        uint16_t P3 = M47 ^ M50;
        uint16_t P4 = M48 ^ M56;
        uint16_t P5 = M46 ^ M51;
        uint16_t P6 = M49 ^ M60;
        uint16_t P7 = P0 ^ P1;
        uint16_t P8 = M50 ^ M53;
        uint16_t P9 = M55 ^ M63;
        uint16_t P10 = M57 ^ P4;
        uint16_t P11 = P0 ^ P3;
        uint16_t P12 = M46 ^ M48;
        uint16_t P13 = M49 ^ M51;
        uint16_t P14 = M49 ^ M62;
        uint16_t P15 = M54 ^ M59;
        uint16_t P16 = M57 ^ M61;
        uint16_t P17 = M58 ^ P2;
        uint16_t P18 = M63 ^ P5;
        uint16_t P19 = P2 ^ P3;
        uint16_t P20 = P4 ^ P6;
        uint16_t P22 = P2 ^ P7;
        uint16_t P23 = P7 ^ P8;
        uint16_t P24 = P5 ^ P7;
        uint16_t P25 = P6 ^ P10;
        uint16_t P26 = P9 ^ P11;
        uint16_t P27 = P10 ^ P18;
        uint16_t P28 = P11 ^ P25;
        uint16_t P29 = P15 ^ P20;
        s->slice[7] = P13 ^ P22;
        s->slice[6] = P26 ^ P29;
        s->slice[5] = P17 ^ P28;
        s->slice[4] = P12 ^ P22;
        s->slice[3] = P23 ^ P27;
        s->slice[2] = P19 ^ P24;
        s->slice[1] = P14 ^ P23;
        s->slice[0] = P9 ^ P16;
    } else {
        /* Linear postprocessing */
        uint16_t L0 = M61 ^ M62;
        uint16_t L1 = M50 ^ M56;
        uint16_t L2 = M46 ^ M48;
        uint16_t L3 = M47 ^ M55;
        uint16_t L4 = M54 ^ M58;
        uint16_t L5 = M49 ^ M61;
        uint16_t L6 = M62 ^ L5;
        uint16_t L7 = M46 ^ L3;
        uint16_t L8 = M51 ^ M59;
        uint16_t L9 = M52 ^ M53;
        uint16_t L10 = M53 ^ L4;
        uint16_t L11 = M60 ^ L2;
        uint16_t L12 = M48 ^ M51;
        uint16_t L13 = M50 ^ L0;
        uint16_t L14 = M52 ^ M61;
        uint16_t L15 = M55 ^ L1;
        uint16_t L16 = M56 ^ L0;
        uint16_t L17 = M57 ^ L1;
        uint16_t L18 = M58 ^ L8;
        uint16_t L19 = M63 ^ L4;
        uint16_t L20 = L0 ^ L1;
        uint16_t L21 = L1 ^ L7;
        uint16_t L22 = L3 ^ L12;
        uint16_t L23 = L18 ^ L2;
        uint16_t L24 = L15 ^ L9;
        uint16_t L25 = L6 ^ L10;
        uint16_t L26 = L7 ^ L9;
        uint16_t L27 = L8 ^ L10;
        uint16_t L28 = L11 ^ L14;
        uint16_t L29 = L11 ^ L17;
        s->slice[7] = L6 ^ L24;
        s->slice[6] = ~(L16 ^ L26);
        s->slice[5] = ~(L19 ^ L28);
        s->slice[4] = L6 ^ L21;
        s->slice[3] = L20 ^ L22;
        s->slice[2] = L25 ^ L29;
        s->slice[1] = ~(L13 ^ L27);
        s->slice[0] = ~(L6 ^ L23);
    }
}

/* Apply the SubBytes transform to the bytes of an unsliced word */
static uint32_t SubWord(uint32_t x) {
    AES_state s;
    int b;
    uint32_t r = 0;
    /* Convert to sliced form */
    for (b = 0; b < 8; b++) {
        s.slice[b] = (x & 1) | ((x >> 7) & 2) | ((x >> 14) & 4) | ((x >> 21) & 8);
        x >>= 1;
    }
    /* Apply the transformation in sliced form */
    SubBytes(&s, 0);
    /* Convert back to word form */
    for (b = 0; b < 8; b++) {
        uint32_t t = s.slice[b];
        r |= ((t & 1) | (t & 2) << 7 | (t & 4) << 14 | (t & 8) << 21) << b;
    }
    return r;
}

static void ShiftRows(AES_state* s) {
    int i;
    for (i = 0; i < 8; i++) {
        uint16_t v = s->slice[i];
        s->slice[i] = (v & 0xF) | (v & 0x10) << 3 | (v & 0xE0) >> 1 | (v & 0x300) << 2 | (v & 0xC00) >> 2 | (v & 0x7000) << 1 | (v & 0x8000) >> 3;
    }
}

static void InvShiftRows(AES_state* s) {
    int i;
    for (i = 0; i < 8; i++) {
        uint16_t v = s->slice[i];
        s->slice[i] = (v & 0xF) | (v & 0x70) << 1 | (v & 0x80) >> 3 | (v & 0x300) << 2 | (v & 0xC00) >> 2 | (v & 0x1000) << 3 | (v & 0xE000) >> 1;
    }
}

#define ROT(x,b) (((x) >> ((b) * 4)) | ((x) << ((4-(b)) * 4)))

static void MixColumns(AES_state* s) {
    /* b(r,c) = 02 * a(r,c) + 02 * a(r+1,c) + a(r+1,c) + a(r+2,c) + a(r+3,c) */
    uint16_t a123[8];
    uint16_t a01[8];
    int i;

    for (i = 0; i < 8; i++) {
        uint16_t a;
        a = s->slice[i];
        a01[i] = a ^ ROT(a,1);
        a123[i] = ROT(a01[i],1) ^ ROT(a, 3);
    }

    s->slice[0] = a01[7] ^ a123[0];
    s->slice[1] = a01[7] ^ a01[0] ^ a123[1];
    s->slice[2] = a01[1] ^ a123[2];
    s->slice[3] = a01[7] ^ a01[2] ^ a123[3];
    s->slice[4] = a01[7] ^ a01[3] ^ a123[4];
    s->slice[5] = a01[4] ^ a123[5];
    s->slice[6] = a01[5] ^ a123[6];
    s->slice[7] = a01[6] ^ a123[7];
}

static void InvMixColumns(AES_state* s) {
    /* b(r,c) = 0e * a(r,c) + 0b * a(r+1,c) + 0d * a(r+2,c) + 09 * a(r+3,c)
     * b(r,c) = 08 * (a(r,c) + a(r+1,c) + a(r+2,c) + a(r+3,c)) +
     *          04 * (a(r,c) + a(r+2,c)) +
     *          02 * (a(r,c) + a(r+1,c)) +
     *          01 * (a(r+1,c) + a(r+2,c) + a(r+3,c))
     */
    uint16_t a01[8];
    uint16_t a12[8];
    uint16_t a123[8];
    uint16_t a0123[8];
    uint16_t a02[8];
    int i;

    for (i = 0; i < 8; i++) {
        uint16_t a;
        a = s->slice[i];
        a01[i] = a ^ ROT(a,1);
        a12[i] = ROT(a01[i], 1);
        a123[i] = a12[i] ^ ROT(a, 3);
        a0123[i] = a ^ a123[i];
        a02[i] = a01[i] ^ a12[i];
    }

    s->slice[0] = a123[0] ^ a01[7] ^ a02[6] ^ a0123[5];
    s->slice[1] = a123[1] ^ a01[0] ^ a12[7] ^ a02[6] ^ a0123[5] ^ a0123[6];
    s->slice[2] = a123[2] ^ a01[1] ^ a02[0] ^ a02[7] ^ a0123[6] ^ a0123[7];
    s->slice[3] = a123[3] ^ a01[2] ^ a01[7] ^ a02[1] ^ a02[6] ^ a0123[0] ^ a0123[5] ^ a0123[7];
    s->slice[4] = a123[4] ^ a01[3] ^ a12[7] ^ a02[2] ^ a02[6] ^ a0123[1] ^ a0123[5] ^ a0123[6];
    s->slice[5] = a123[5] ^ a01[4] ^ a02[3] ^ a02[7] ^ a0123[2] ^ a0123[6] ^ a0123[7];
    s->slice[6] = a123[6] ^ a01[5] ^ a02[4] ^ a0123[3] ^ a0123[7];
    s->slice[7] = a123[7] ^ a01[6] ^ a02[5] ^ a0123[4];
}

void AddRoundKey(AES_state* s, const AES_state* round) {
    int b;
    for (b = 0; b < 8; b++) {
        s->slice[b] ^= round->slice[b];
    }
}

/** Expand the cipher key into the key schedule.
 *
 *  state must be a pointer to an array of size nrounds + 1.
 *  key must be a pointer to 4 * nkeywords bytes.
 *
 *  AES128 uses nkeywords = 4, nrounds = 10
 *  AES192 uses nkeywords = 6, nrounds = 12
 *  AES256 uses nkeywords = 8, nrounds = 14
 */
static void AES_setup(AES_state* rounds, const uint8_t* key, int nkeywords, int nrounds)
{
    int i;

    /* The one-byte round constant */
    uint8_t rcon = 0x01;
    /* A ring buffer containing the last 8 round key words (4 are consumed in every round) */
    uint32_t rk[8];
    /* The number of the word being generated, modulo nkeywords */
    int pos = 0;

    /* The first nkeywords round key words are just taken from the key directly */
    for (i = 0; i < nkeywords; i++) {
        rk[i] = ((uint32_t)key[0]) << 24 | ((uint32_t)key[1]) << 16 | ((uint32_t)key[2]) << 8 | key[3];
        if ((i & 3) == 3) {
            /* If we've generated 4 round key words, convert them to sliced form for use in one round */
            LoadWords(rounds++, rk[i - 3], rk[i - 2], rk[i - 1], rk[i]);
        }
        key += 4;
    }

    for (i = nkeywords; i < 4 * (nrounds + 1); i++) {
        /* Get the previous round word */
        uint32_t temp = rk[(i + 7) & 7];
        /* Transform temp */
        if (pos == 0) {
            temp = SubWord(temp << 8 | temp >> 24) ^ ((uint32_t)rcon) << 24;
            /* Compute the next round constant (multiply by x modulo x^8 + x^4 + x^3 + x + 1) */
            rcon = ((-(rcon >> 7)) & 0x1B) ^ (rcon << 1);
        } else if (nkeywords > 6 && pos == 4) {
            temp = SubWord(temp);
        }
        if (++pos == nkeywords) pos = 0;
        /* Compute the next round key word */
        rk[i & 7] = rk[(i + 8 - nkeywords) & 7] ^ temp;
        if ((i & 3) == 3) {
            /* If we've generated 4 round key words, convert them to sliced form for use in one round */
            LoadWords(rounds++, rk[(i + 5) & 7], rk[(i + 6) & 7], rk[(i + 7) & 7], rk[i & 7]);
        }
    }
}

static void AES_encrypt(const AES_state* rounds, int nrounds, unsigned char* cipher16, const unsigned char* plain16) {
    AES_state s;
    int round;

    LoadBytes(&s, plain16);
    AddRoundKey(&s, rounds++);

    for (round = 1; round < nrounds; round++) {
        SubBytes(&s, 0);
        ShiftRows(&s);
        MixColumns(&s);
        AddRoundKey(&s, rounds++);
    }

    SubBytes(&s, 0);
    ShiftRows(&s);
    AddRoundKey(&s, rounds);

    SaveBytes(cipher16, &s);
}

static void AES_decrypt(const AES_state* rounds, int nrounds, unsigned char* plain16, const unsigned char* cipher16) {
    /* Most AES decryption implementations use the alternate scheme
     * (the Equivalent Inverse Cipher), which looks more like encryption, but
     * needs different round constants. We can't reuse any code here anyway, so
     * don't bother. */
    AES_state s;
    int round;

    rounds += nrounds;

    LoadBytes(&s, cipher16);
    AddRoundKey(&s, rounds--);

    for (round = 1; round < nrounds; round++) {
        InvShiftRows(&s);
        SubBytes(&s, 1);
        AddRoundKey(&s, rounds--);
        InvMixColumns(&s);
    }

    InvShiftRows(&s);
    SubBytes(&s, 1);
    AddRoundKey(&s, rounds);

    SaveBytes(plain16, &s);
}

void AES128_init(AES128_ctx* ctx, const unsigned char* key16) {
    AES_setup(ctx->rk, key16, 4, 10);
}

void AES128_encrypt(const AES128_ctx* ctx, unsigned char* cipher16, const unsigned char* plain16) {
    AES_encrypt(ctx->rk, 10, cipher16, plain16);
}

void AES128_decrypt(const AES128_ctx* ctx, unsigned char* plain16, const unsigned char* cipher16) {
    AES_decrypt(ctx->rk, 10, plain16, cipher16);
}

void AES192_init(AES192_ctx* ctx, const unsigned char* key24) {
    AES_setup(ctx->rk, key24, 6, 12);
}

void AES192_encrypt(const AES192_ctx* ctx, unsigned char* cipher16, const unsigned char* plain16) {
    AES_encrypt(ctx->rk, 12, cipher16, plain16);
}

void AES192_decrypt(const AES192_ctx* ctx, unsigned char* plain16, const unsigned char* cipher16) {
    AES_decrypt(ctx->rk, 12, plain16, cipher16);
}

void AES256_init(AES256_ctx* ctx, const unsigned char* key32) {
    AES_setup(ctx->rk, key32, 8, 14);
}

void AES256_encrypt(const AES256_ctx* ctx, unsigned char* cipher16, const unsigned char* plain16) {
    AES_encrypt(ctx->rk, 14, cipher16, plain16);
}

void AES256_decrypt(const AES256_ctx* ctx, unsigned char* plain16, const unsigned char* cipher16) {
    AES_decrypt(ctx->rk, 14, plain16, cipher16);
}

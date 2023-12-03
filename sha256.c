//usr/bin/env clang -Ofast -Wall -Wextra -pedantic ${0} -o ${0%%.c*} $* ;exit $?
//
//  SHA-256 implementation, Mark 2
//
//  Copyright (c) 2010,2014 Literatecode, http://www.literatecode.com
//  Copyright (c) 2022 Ilia Levin (ilia@levin.sg)
//
//  Permission to use, copy, modify, and distribute this software for any
//  purpose with or without fee is hereby granted, provided that the above
//  copyright notice and this permission notice appear in all copies.
//
//  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
//  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
//  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
//  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
//  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
//  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
//  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
//

#include "sha256.h"

#ifndef _cbmc_
#define __CPROVER_assume(...) do {} while(0)
#endif

#ifdef __cplusplus
extern "C" {
#endif

#define FN_ static inline __attribute__((const))

static const uint32_t K[64] = {
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
    0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
    0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
    0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
    0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
    0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
};


// -----------------------------------------------------------------------------
FN_ uint8_t _shb(uint32_t x, uint32_t n)
{
    return ((x >> (n & 31)) & 0xff);
} // _shb


// -----------------------------------------------------------------------------
FN_ uint32_t _shw(uint32_t x, uint32_t n)
{
    return ((x << (n & 31)) & 0xffffffff);
} // _shw


// -----------------------------------------------------------------------------
FN_ uint32_t _r(uint32_t x, uint8_t n)
{
    return ((x >> n) | _shw(x, 32 - n));
} // _r


// -----------------------------------------------------------------------------
FN_ uint32_t _Ch(uint32_t x, uint32_t y, uint32_t z)
{
    return ((x & y) ^ ((~x) & z));
} // _Ch


// -----------------------------------------------------------------------------
FN_ uint32_t _Ma(uint32_t x, uint32_t y, uint32_t z)
{
    return ((x & y) ^ (x & z) ^ (y & z));
} // _Ma


// -----------------------------------------------------------------------------
FN_ uint32_t _S0(uint32_t x)
{
    return (_r(x, 2) ^ _r(x, 13) ^ _r(x, 22));
} // _S0


// -----------------------------------------------------------------------------
FN_ uint32_t _S1(uint32_t x)
{
    return (_r(x, 6) ^ _r(x, 11) ^ _r(x, 25));
} // _S1


// -----------------------------------------------------------------------------
FN_ uint32_t _G0(uint32_t x)
{
    return (_r(x, 7) ^ _r(x, 18) ^ (x >> 3));
} // _G0


// -----------------------------------------------------------------------------
FN_ uint32_t _G1(uint32_t x)
{
    return (_r(x, 17) ^ _r(x, 19) ^ (x >> 10));
} // _G1


// -----------------------------------------------------------------------------
FN_ uint32_t _word(uint8_t *c)
{
    return (_shw(c[0], 24) | _shw(c[1], 16) | _shw(c[2], 8) | (c[3]));
} // _word


// -----------------------------------------------------------------------------
static void _addbits(sha256_context *ctx, uint32_t n)
{
    __CPROVER_assume(__CPROVER_DYNAMIC_OBJECT(ctx));

    if (ctx->bits[0] > (0xffffffff - n)) {
        ctx->bits[1] = (ctx->bits[1] + 1) & 0xFFFFFFFF;
    }
    ctx->bits[0] = (ctx->bits[0] + n) & 0xFFFFFFFF;
} // _addbits


// -----------------------------------------------------------------------------
static void _hash(sha256_context *ctx)
{
    __CPROVER_assume(__CPROVER_DYNAMIC_OBJECT(ctx));

    register uint32_t a, b, c, d, e, f, g, h;
    uint32_t t[2];

    a = ctx->hash[0];
    b = ctx->hash[1];
    c = ctx->hash[2];
    d = ctx->hash[3];
    e = ctx->hash[4];
    f = ctx->hash[5];
    g = ctx->hash[6];
    h = ctx->hash[7];

    for (uint32_t i = 0; i < 64; i++) {
        if (i < 16) {
            ctx->W[i] = _word(&ctx->buf[_shw(i, 2)]);
        } else {
            ctx->W[i] = _G1(ctx->W[i - 2])  + ctx->W[i - 7] +
                        _G0(ctx->W[i - 15]) + ctx->W[i - 16];
        }

        t[0] = h + _S1(e) + _Ch(e, f, g) + K[i] + ctx->W[i];
        t[1] = _S0(a) + _Ma(a, b, c);
        h = g;
        g = f;
        f = e;
        e = d + t[0];
        d = c;
        c = b;
        b = a;
        a = t[0] + t[1];
    }

    ctx->hash[0] += a;
    ctx->hash[1] += b;
    ctx->hash[2] += c;
    ctx->hash[3] += d;
    ctx->hash[4] += e;
    ctx->hash[5] += f;
    ctx->hash[6] += g;
    ctx->hash[7] += h;
} // _hash


// -----------------------------------------------------------------------------
void sha256_init(sha256_context *ctx)
{
    if (ctx != NULL) {
        ctx->bits[0] = ctx->bits[1] = ctx->len = 0;
        ctx->hash[0] = 0x6a09e667;
        ctx->hash[1] = 0xbb67ae85;
        ctx->hash[2] = 0x3c6ef372;
        ctx->hash[3] = 0xa54ff53a;
        ctx->hash[4] = 0x510e527f;
        ctx->hash[5] = 0x9b05688c;
        ctx->hash[6] = 0x1f83d9ab;
        ctx->hash[7] = 0x5be0cd19;
    }
} // sha256_init


// -----------------------------------------------------------------------------
void sha256_hash(sha256_context *ctx, const void *data, size_t len)
{
    const uint8_t *bytes = (const uint8_t *)data;

    if ((ctx != NULL) && (bytes != NULL) && (ctx->len < sizeof(ctx->buf))) {
        __CPROVER_assume(__CPROVER_DYNAMIC_OBJECT(bytes));
        __CPROVER_assume(__CPROVER_DYNAMIC_OBJECT(ctx));
        for (size_t i = 0; i < len; i++) {
            ctx->buf[ctx->len++] = bytes[i];
            if (ctx->len == sizeof(ctx->buf)) {
                _hash(ctx);
                _addbits(ctx, sizeof(ctx->buf) * 8);
                ctx->len = 0;
            }
        }
    }
} // sha256_hash


// -----------------------------------------------------------------------------
void sha256_done(sha256_context *ctx, uint8_t *hash)
{
    register uint32_t i, j;

    if (ctx != NULL) {
        j = ctx->len % sizeof(ctx->buf);
        ctx->buf[j] = 0x80;
        for (i = j + 1; i < sizeof(ctx->buf); i++) {
            ctx->buf[i] = 0x00;
        }

        if (ctx->len > 55) {
            _hash(ctx);
            for (j = 0; j < sizeof(ctx->buf); j++) {
                ctx->buf[j] = 0x00;
            }
        }

        _addbits(ctx, ctx->len * 8);
        ctx->buf[63] = _shb(ctx->bits[0],  0);
        ctx->buf[62] = _shb(ctx->bits[0],  8);
        ctx->buf[61] = _shb(ctx->bits[0], 16);
        ctx->buf[60] = _shb(ctx->bits[0], 24);
        ctx->buf[59] = _shb(ctx->bits[1],  0);
        ctx->buf[58] = _shb(ctx->bits[1],  8);
        ctx->buf[57] = _shb(ctx->bits[1], 16);
        ctx->buf[56] = _shb(ctx->bits[1], 24);
        _hash(ctx);

        if (hash != NULL) {
            for (i = 0, j = 24; i < 4; i++, j -= 8) {
                hash[i +  0] = _shb(ctx->hash[0], j);
                hash[i +  4] = _shb(ctx->hash[1], j);
                hash[i +  8] = _shb(ctx->hash[2], j);
                hash[i + 12] = _shb(ctx->hash[3], j);
                hash[i + 16] = _shb(ctx->hash[4], j);
                hash[i + 20] = _shb(ctx->hash[5], j);
                hash[i + 24] = _shb(ctx->hash[6], j);
                hash[i + 28] = _shb(ctx->hash[7], j);
            }
        }
    }
} // sha256_done


// -----------------------------------------------------------------------------
void sha256(const void *data, size_t len, uint8_t *hash)
{
    sha256_context ctx;

    sha256_init(&ctx);
    sha256_hash(&ctx, data, len);
    sha256_done(&ctx, hash);
} // sha256


#if 0
#pragma mark - Self Test
#endif
#ifdef SHA256_SELF_TEST__
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int main(void)
{
    char *buf[] = {
        "",
        "e3b0c442 98fc1c14 9afbf4c8 996fb924 27ae41e4 649b934c a495991b 7852b855",

        "abc",
        "ba7816bf 8f01cfea 414140de 5dae2223 b00361a3 96177a9c b410ff61 f20015ad",

        "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
        "248d6a61 d20638b8 e5c02693 0c3e6039 a33ce459 64ff2167 f6ecedd4 19db06c1",

        "The quick brown fox jumps over the lazy dog",
        "d7a8fbb3 07d78094 69ca9abc b0082e4f 8d5651e4 6d3cdb76 2d02d0bf 37c9e592",

        "The quick brown fox jumps over the lazy cog", // avalanche effect test
        "e4c4d8f3 bf76b692 de791a17 3e053211 50f7a345 b46484fe 427f6acc 7ecc81be",

        "bhn5bjmoniertqea40wro2upyflkydsibsk8ylkmgbvwi420t44cq034eou1szc1k0mk46oeb7ktzmlxqkbte2sy",
        "9085df2f 02e0cc45 5928d0f5 1b27b4bf 1d9cd260 a66ed1fd a11b0a3f f5756d99",

	"awehuijot;n",
	"",

	"adtyjtdyjtvbnmiohp;up2a",
	"",

	"124780247t689sehuijy;baejk4;ahuihs,bn",
	"",
	
	"huio;aw4ibnxcvjbk;",
	"",

	"uioaehr;'23589yuihjldh;z[]]\"",
	"",
	
	"uohwetjbna;p;aw48h935njklzfbbjikZklathjjkg",
	"",

	"zdfhaer5yhxfgnmcuj,gguo/guo0;']9-_+-",
	"",

	"{!aeo5ui;hynjekray9o4u8ai3h6jbnjthiap;ey480a4hyijkh@#at4uweiotbej4ktw489htejkbhej$",
	"",

	"}\%se5tyhsr^kdtukyudlkuy&oliyl;fyil*fl(",
	"",

	"|aw4t79yh4tujlba.jghkae;h9w4otu))_+atehtjutktygweq\"qqyjsrtyktyiop\'zxfgnjfghxvbmvhmj,zxdhzw",
	"",

	"asdrgjklrwhbn\\ atgujker;bgjkadg;ae7894u3hoa~`",
	"",

	"?sery/aasdhjklgadrkjgol'zbnm,4ito;h",
	"",

	"seryersu<&jkyrskul*diktyukouklughjqwwetrtrytuyuiouiou9p>",
	"",

	"se5rthyraerthuthutjyrtjkjrsiklhjnw4t69230ha4lwbhnaejrkqaw3ubgiltuha34bgtvuiw4ptagew89yhcjvbjw4ilpta8ay3ht4;ujabrghkrdbilaw;34tuo;aegh4rjtuyabehr;",
	"",
	
	"iawrohtgnejlrw;bghnyuiopw4;aatyaaahi8aa34aaaauaty6aaaaeop4rghuydfjukbghvzdfjknb.dnszmgbz,.rsdmfgnewklt;rqi3kopteiowtp[23905t8u2-395=24967[95wy6i54etES%RGTYAHERITHNEW$JKLRBGNYE$IPR(TYAW4",
	"",

	"TSE4IO5;HTGNJAEKRL.GTEHRUWAIOP;TEHRWBAJNTYKW4.TYJ4W/TO3Q;'5O2Q18'4590230;Y5HTABW4TJKW4;TYIOE;AHIKYGHAENRJKGHABER; HTU AHJKRW4 TUAW4HORTUILE4 TUAHW4.JTHW348OTY",
	"",

	"AW4IOP'HTYIW3wet4w4rtytutyNY/JL3W4AAATtyiyi;AAAtyityiA9A7AUWetutu3erhfgAjfhkhujlyhuiloiApAA50AAAA-AA2AQAA[A590Y;AOU3uiosh;e5nrbjyao;3489yt6a3",
	"",

	"uw4io;aty hujekrlRAEGYHJIER%NYKL$WAY:APW$_{TA$#Ueauth;ebjrkt;w4y8tyhw4ehrbtjAWETUJAW#@#*UTJKRTLHJNFTYGKLJNMFXG(XUiseruyihjpu",
	"",

	"uowtyhueowtpqeuiroepwtu[]erty9oeruioyjdrkgly;ehrgjakldhgjk.fnbmz,.fm.ncvxm,bm/dfl;cmvz,./msdkg'eruigt'ueirh'agkreghzDERJGZIjrezkGJKDNRGHEIRZGHJ",
	"",

	"WERAZHGIOTHerhjtagj;ergjykaer;AERHJGYIKLAkjDR:gBNNMgjkKOosdrGsdgdgjkyTdt6y73e45@#4t6u689o8900[FGNJ",
	"",

	"QRTSGhZTGZHbFYJNMghjm,DGKTU<hjYIFOLFUI(LPT&(P:rf79op%&UIrryujETYUWERTqetQWETsdrgzsfbhXFNXFGNZDBzfbxfv nXVNMCBMvn,vn,bj.mhk.gjluo;uo;'io[yhul",
	"",

	"UIHW#ERGJKBRT#OUY*BJLQW@HJKLESHIJPR&(_BFHIPTW$EKLN:KN:>TW$IO{WER$Y*)+WRGHJKL:WR:BHKNFIOPBHK:RSGHL:RSDG>?DS>?TL:EJSMGT<>EDS>?FG<ESWTGP{EWTG{PEW}TEW}|T{EW}|T*)_EWPTU(EKNW:GRW",
	"",

	"SE*(OHWE$TJKHEST*(IO#THJLETFP*(G){BR_}RWE(\"EW&*()TIOEHWG*)EWRGEWIPhio*){\"EGRBJLOGRO*{ERBGJLEWO*:T",
	"",

	"htsrjyklnjekrty;ERTGwrjkhetKSHejtkhTshrRTMJK:RTY$\%EO)7^&*^&()*(P_W$etRWTGYrfsHdtgjETj",
	"",
	"||\\//hierklnkr\\tgwhnejkltgbnwjo4;thesu5jyk//ersigjlyn||yikghnae5jkly;ae9i5jyaklynioer;ahyjndfjkRESYHIOERAJHYIKLBEHNAILOBGHEIORH\\|srttj|/aetrherth/",
	"",

	"tsrkhjlnukelnyerioyhhnethks\\egyo;kjr5yo3e45-y0=_",
	"",

	"srrtsjtsjy,ytkstkl\"usrtj::,ltUSRTOI$OEAYNMK#$LAIOJNKLH",
	"",

	"ujerksh;yjresbnyjo;eyAEYRJIOAYEJKNAERHaylkejrkyaerjjkyehrailhyejkrany4aoy8ah4it6h34890yh",
	"",

	"jkernyjestnhyklt",
	"",

	"iykjne5ktlsn/",
	"",

	"sr5tiopuhjklrthu",
	"",

	"tsrto;j'hmuklrtjkloes;t5hjyiket5S%YHJIEJRTHIKLYER\%AIOYHJUEOP%j",
	"",

	"jlaerk;hnyjeklt.yheijruhny;aAERJYRWEJIYJWneraikerhnjklyhaekoruyhaernjnjoaeyAERYHIJKer",
	""
    };
    const size_t tests_total = sizeof(buf) / sizeof(buf[0]);
    uint8_t hash[SHA256_SIZE_BYTES];
    
    const size_t modifier = 10000000;
    int elements = 100000;
    long double nums[elements];

    if (0 != (tests_total % 2)) {
        return printf("invalid tests\n");
    }
    for (size_t jj = 0; jj < modifier; jj++) {
	printf("Begin jj or modifier=10000000 loop\n");
	if(rand()%100 <= 50){
	    continue;
	}
	for(int nElem=0; nElem < elements; nElem++){
	    if(rand()%100 <= 50){
	        nums[nElem] = (long double)((rand()%modifier)/11);
		continue;
	    }
	    nums[nElem] = (long double)(jj+(rand()%modifier)/(3*(nElem+1)));
	}
        for (size_t i2 = 0; i2 < tests_total; i2 += 2) {
	    char appendString[30*elements+10*elements];
	    char placeHolder[30];
	    printf("Begin i2=tests_total increment by 2 loop\n");

            for(int nElem=(int)(elements/2); nElem < elements; nElem++){
	        nums[nElem] = (long double)(i2+(rand()%modifier)/(7*(nElem+1)));
            }
	    sprintf(appendString, "%.20Lf",nums[0]);
	    for(int nElem=1; nElem < elements; nElem++){
	        sprintf(placeHolder, "%.20Lf",nums[nElem]);
	        strcat(appendString, placeHolder);
	    }
	    for(int r=0; r < elements; r++){
		if(rand()%10 <= 7){
		    continue;
		}
                sprintf(placeHolder, "%d", rand()%10000000000);
                strcat(appendString, placeHolder);
            }

	    size_t i=(size_t)(rand()%tests_total);
	    if (i%2!=0){
		if (i<tests_total-1){
		    i++;
		}else{
		    i=0;
		}
            }
	    int length = strlen(buf[i])+(30*elements+10*elements);
	    printf("Length: %d\n",length);
	    char s[length];
	    sprintf(s, "%s", buf[i]);
	    printf("original: %s\n",s);
	    strcat(s, appendString);
	    printf("AppendString starts with: ");
	    for(int start = 0; start < 10; start++){
	        printf("%c",appendString[start]);
	    }
	    printf("\n");
	    printf("AppendString ends with: ");
	    for(int start = strlen(appendString)-10; start < strlen(appendString); start++){
	        printf("%c",appendString[start]);
	    }
	    printf("\n");
            sha256(s, strlen(s), hash);
            printf("input = '%s'\nresult: ", s);
            //printf("input = '%s'\ndigest: %s\nresult: ", s, buf[i + 1]);
            for (size_t j = 0; j < SHA256_SIZE_BYTES; j++) {
                printf("%02x%s", hash[j], ((j % 4) == 3) ? " " : "");
            }
            printf("\n\n");
        }
    }

    return 0;
} // main

#endif // def SHA256_SELF_TEST__

#ifdef __cplusplus
}
#endif

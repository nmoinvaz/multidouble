// ldf_bench.c -- LIB-Dekker-Float side of the comparison. Float64x2 and Float64x4, C99 API, header-only arithmetic.
//
//   ldf_bench time DATADIR        timing, one JSON line per (op, mode) on stdout
//   ldf_bench acc  DATADIR OUTDIR results of every op on the whole input set, raw f64, for acc_eval.py
//
// Throughput: out[i] = op(a[i], b[i]) over N_T independent elements. Latency: x = op(x, b[i]) in one dependent chain
// (unary ops: blocks of 32 steps, each block's start tied to the previous result by + 0 * x). A compiler barrier
// (asm memory clobber) after every repetition forces each repetition to reload the operands and redo the work.

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#include "Float64x4/Float64x4.h"

#ifndef PREFIX
#define PREFIX "ldf"
#endif

#define N_T 512
#define SAMPLES 31
#define TARGET_NS 300000.0
#define BLOCK 32

#define BARRIER() __asm__ volatile("" ::: "memory")
// v is read and rewritten by the asm, so the chain that produced it cannot be dropped
#define SINK(v) __asm__ volatile("" : "+w"(v) : : "memory")
#define NOINLINE __attribute__((noinline))

typedef Float64x2 D2;
typedef Float64x4 D4;

static uint64_t now_ns(void) { return clock_gettime_nsec_np(CLOCK_UPTIME_RAW); }

static double* load(const char* dir, const char* name, size_t* count) {
    char path[1024];
    snprintf(path, sizeof path, "%s/%s.bin", dir, name);
    FILE* fh = fopen(path, "rb");
    if (!fh) { fprintf(stderr, "cannot open %s\n", path); exit(1); }
    fseek(fh, 0, SEEK_END);
    long len = ftell(fh);
    fseek(fh, 0, SEEK_SET);
    double* v = malloc((size_t)len);
    if (fread(v, 1, (size_t)len, fh) != (size_t)len) { fprintf(stderr, "short read %s\n", path); exit(1); }
    fclose(fh);
    *count = (size_t)len / sizeof(double);
    return v;
}

static void save(const char* dir, const char* name, const double* v, size_t count) {
    char path[1024];
    snprintf(path, sizeof path, "%s/%s_%s.bin", dir, PREFIX, name);
    FILE* fh = fopen(path, "wb");
    if (!fh) { fprintf(stderr, "cannot write %s\n", path); exit(1); }
    fwrite(v, sizeof(double), count, fh);
    fclose(fh);
}

static D2 abs2(D2 x) { return x.hi < 0.0 ? Float64x2_negate(x) : x; }
static D4 abs4(D4 x) { return x.val[0] < 0.0 ? Float64x4_negate(x) : x; }

// ---------------------------------------------------------------------------------------------------------------------
// kernels: a, b are the operands, f a double

#define DD_OPS(X)                                   \
    X(dd_add, Float64x2_add(a, b))                  \
    X(dd_sub, Float64x2_sub(a, b))                  \
    X(dd_mul, Float64x2_mul(a, b))                  \
    X(dd_div, Float64x2_div(a, b))                  \
    X(dd_mul_f, Float64x2_mul_dx2_d(a, f))

#define QD_OPS(X)                                    \
    X(qd_add_sloppy, Float64x4_add_quick(a, b))      \
    X(qd_add_ieee, Float64x4_add_accurate(a, b))     \
    X(qd_sub_sloppy, Float64x4_sub_quick(a, b))      \
    X(qd_sub_ieee, Float64x4_sub_accurate(a, b))     \
    X(qd_mul_sloppy, Float64x4_mul_quick(a, b))      \
    X(qd_mul_accurate, Float64x4_mul_accurate(a, b)) \
    X(qd_div_sloppy, Float64x4_div_quick(a, b))      \
    X(qd_div_accurate, Float64x4_div_accurate(a, b)) \
    X(qd_mul_f, Float64x4_mul_dx4_d(a, f))           \
    X(qd_add_f, Float64x4_add_dx4_d(a, f))

#define DD_UN(X) X(dd_sqrt, Float64x2_sqrt(a))
#define QD_UN(X) X(qd_sqrt, Float64x4_sqrt(a))

#define DEF_BIN(T, HI, name, EXPR)                                                                                      \
    static NOINLINE void thr_##name(const T* restrict A, const T* restrict B, const double* restrict F,            \
                                    T* restrict O, int n, long reps) {                                             \
        for (long r = 0; r < reps; r++) {                                                                          \
            for (int i = 0; i < n; i++) {                                                                          \
                const T a = A[i];                                                                                  \
                const T b = B[i];                                                                                  \
                const double f = F[i];                                                                             \
                (void)b;                                                                                           \
                (void)f;                                                                                           \
                O[i] = (EXPR);                                                                                     \
            }                                                                                                      \
            BARRIER();                                                                                             \
        }                                                                                                          \
    }                                                                                                              \
    static NOINLINE T lat_##name(T x0, const T* restrict B, const double* restrict F, int n, long reps) {           \
        T x = x0;                                                                                                  \
        for (long r = 0; r < reps; r++) {                                                                          \
            x = x0;                                                                                                \
            for (int i = 0; i < n; i++) {                                                                          \
                const T a = x;                                                                                     \
                const T b = B[i];                                                                                  \
                const double f = F[i];                                                                             \
                (void)b;                                                                                           \
                (void)f;                                                                                           \
                x = (EXPR);                                                                                        \
            }                                                                                                      \
            SINK(x.HI);                                                                                            \
        }                                                                                                          \
        return x;                                                                                                  \
    }

#define DEF_UN(T, HI, name, EXPR)                                                                                   \
    static NOINLINE void thr_##name(const T* restrict A, T* restrict O, int n, long reps) {                        \
        for (long r = 0; r < reps; r++) {                                                                          \
            for (int i = 0; i < n; i++) {                                                                          \
                const T a = A[i];                                                                                  \
                O[i] = (EXPR);                                                                                     \
            }                                                                                                      \
            BARRIER();                                                                                             \
        }                                                                                                          \
    }                                                                                                              \
    static NOINLINE T lat_##name(const T* restrict A, int n, long reps) {                                          \
        T x = A[0];                                                                                                \
        for (long r = 0; r < reps; r++) {                                                                          \
            for (int i = 0; i < n; i += BLOCK) {                                                                   \
                T s = A[i];                                                                                        \
                s.HI = s.HI + 0.0 * x.HI;                                                                          \
                x = s;                                                                                             \
                for (int k = 0; k < BLOCK; k++) {                                                                  \
                    const T a = x;                                                                                 \
                    x = (EXPR);                                                                                    \
                }                                                                                                  \
            }                                                                                                      \
            SINK(x.HI);                                                                                            \
        }                                                                                                          \
        return x;                                                                                                  \
    }

#define X_DD(name, EXPR) DEF_BIN(D2, hi, name, EXPR)
#define X_QD(name, EXPR) DEF_BIN(D4, val[0], name, EXPR)
#define X_DDU(name, EXPR) DEF_UN(D2, hi, name, EXPR)
#define X_QDU(name, EXPR) DEF_UN(D4, val[0], name, EXPR)
DD_OPS(X_DD)
QD_OPS(X_QD)
DD_UN(X_DDU)
QD_UN(X_QDU)

// ---------------------------------------------------------------------------------------------------------------------
// timing

static int cmp_double(const void* p, const void* q) {
    double a = *(const double*)p, b = *(const double*)q;
    return (a > b) - (a < b);
}

static double sum2(const D2* v, int n) {
    double s = 0.0;
    for (int i = 0; i < n; i++) s += v[i].hi + v[i].lo;
    return s;
}
static double sum4(const D4* v, int n) {
    double s = 0.0;
    for (int i = 0; i < n; i++) s += v[i].val[0] + v[i].val[1];
    return s;
}

static void report(const char* op, const char* mode, long reps, double* t, double chk) {
    qsort(t, SAMPLES, sizeof(double), cmp_double);
    printf("{\"lib\":\"" PREFIX "\",\"op\":\"%s\",\"mode\":\"%s\",\"n\":%d,\"reps\":%ld,\"samples\":%d,"
           "\"min_ns\":%.4f,\"med_ns\":%.4f,\"max_ns\":%.4f,\"chk\":%.17g}\n",
           op, mode, N_T, reps, SAMPLES, t[0], t[SAMPLES / 2], t[SAMPLES - 1], chk);
    fflush(stdout);
}

// time CALL (which runs `reps` repetitions of N_T element operations) as ns per element operation
#define TIME(op, mode, CALL, CHK)                                                                                  \
    do {                                                                                                           \
        long reps = 1;                                                                                             \
        uint64_t t0 = now_ns();                                                                                    \
        CALL;                                                                                                      \
        double dt = (double)(now_ns() - t0);                                                                       \
        reps = (long)(TARGET_NS / (dt > 1.0 ? dt : 1.0));                                                          \
        if (reps < 1) reps = 1;                                                                                    \
        CALL;                                                                                                      \
        double t[SAMPLES];                                                                                         \
        for (int s = 0; s < SAMPLES; s++) {                                                                        \
            uint64_t a0 = now_ns();                                                                                \
            CALL;                                                                                                  \
            t[s] = (double)(now_ns() - a0) / ((double)reps * N_T);                                                 \
        }                                                                                                          \
        report(op, mode, reps, t, CHK);                                                                            \
    } while (0)

int main(int argc, char** argv) {
    if (argc < 3) {
        fprintf(stderr, "usage: %s time|acc DATADIR [OUTDIR]\n", argv[0]);
        return 2;
    }
    const char* dir = argv[2];
    size_t n_dd, n_qd, n_f, nc;
    double* dda = load(dir, "dd_a", &n_dd);
    double* ddb = load(dir, "dd_b", &nc);
    double* ddca = load(dir, "dd_ca", &nc);
    double* ddcb = load(dir, "dd_cb", &nc);
    double* ddcbn = load(dir, "dd_cbn", &nc);
    double* qda = load(dir, "qd_a", &n_qd);
    double* qdb = load(dir, "qd_b", &nc);
    double* qdca = load(dir, "qd_ca", &nc);
    double* qdcb = load(dir, "qd_cb", &nc);
    double* qdcbn = load(dir, "qd_cbn", &nc);
    double* fv = load(dir, "f", &n_f);
    double* latdd = load(dir, "lat_dd", &nc);
    double* latqd = load(dir, "lat_qd", &nc);
    double* latf = load(dir, "lat_f", &nc);
    int n = (int)n_f;
    D2 *A2 = malloc(sizeof(D2) * n), *B2 = malloc(sizeof(D2) * n), *CA2 = malloc(sizeof(D2) * n),
       *CB2 = malloc(sizeof(D2) * n), *CN2 = malloc(sizeof(D2) * n), *L2 = malloc(sizeof(D2) * n), *S2 = malloc(sizeof(D2) * n),
       *O2 = malloc(sizeof(D2) * n);
    D4 *A4 = malloc(sizeof(D4) * n), *B4 = malloc(sizeof(D4) * n), *CA4 = malloc(sizeof(D4) * n),
       *CB4 = malloc(sizeof(D4) * n), *CN4 = malloc(sizeof(D4) * n), *L4 = malloc(sizeof(D4) * n), *S4 = malloc(sizeof(D4) * n),
       *O4 = malloc(sizeof(D4) * n);
    for (int i = 0; i < n; i++) {
        A2[i] = (D2){dda[2 * i], dda[2 * i + 1]};
        B2[i] = (D2){ddb[2 * i], ddb[2 * i + 1]};
        CA2[i] = (D2){ddca[2 * i], ddca[2 * i + 1]};
        CB2[i] = (D2){ddcb[2 * i], ddcb[2 * i + 1]};
        CN2[i] = (D2){ddcbn[2 * i], ddcbn[2 * i + 1]};
        L2[i] = (D2){latdd[2 * i], latdd[2 * i + 1]};
        S2[i] = abs2(A2[i]);
        for (int k = 0; k < 4; k++) {
            A4[i].val[k] = qda[4 * i + k];
            B4[i].val[k] = qdb[4 * i + k];
            CA4[i].val[k] = qdca[4 * i + k];
            CB4[i].val[k] = qdcb[4 * i + k];
            CN4[i].val[k] = qdcbn[4 * i + k];
            L4[i].val[k] = latqd[4 * i + k];
        }
        S4[i] = abs4(A4[i]);
    }

    if (strcmp(argv[1], "acc") == 0) {
        if (argc < 4) { fprintf(stderr, "acc needs OUTDIR\n"); return 2; }
        const char* out = argv[3];
#define ACC_DD(name, EXPR)                                                                                         \
    thr_##name(A2, B2, fv, O2, n, 1);                                                                              \
    save(out, #name, (const double*)O2, 2 * (size_t)n);                                                           \
    thr_##name(CA2, strstr(#name, "sub") ? CN2 : CB2, fv, O2, n, 1);                                                                            \
    save(out, #name "_c", (const double*)O2, 2 * (size_t)n);
#define ACC_QD(name, EXPR)                                                                                         \
    thr_##name(A4, B4, fv, O4, n, 1);                                                                              \
    save(out, #name, (const double*)O4, 4 * (size_t)n);                                                           \
    thr_##name(CA4, strstr(#name, "sub") ? CN4 : CB4, fv, O4, n, 1);                                                                            \
    save(out, #name "_c", (const double*)O4, 4 * (size_t)n);
#define ACC_DDU(name, EXPR)                                                                                        \
    thr_##name(S2, O2, n, 1);                                                                                      \
    save(out, #name, (const double*)O2, 2 * (size_t)n);
#define ACC_QDU(name, EXPR)                                                                                        \
    thr_##name(S4, O4, n, 1);                                                                                      \
    save(out, #name, (const double*)O4, 4 * (size_t)n);
        DD_OPS(ACC_DD)
        QD_OPS(ACC_QD)
        DD_UN(ACC_DDU)
        QD_UN(ACC_QDU)
        return 0;
    }

    // timing: the first N_T elements; latency chains run over the [0.5, 2) operands
#define T_DD(name, EXPR)                                                                                           \
    TIME(#name, "thr", thr_##name(A2, B2, fv, O2, N_T, reps), sum2(O2, N_T));                                      \
    {                                                                                                              \
        D2 x = L2[0];                                                                                              \
        TIME(#name, "lat", x = lat_##name(L2[N_T], L2, latf, N_T, reps), x.hi + x.lo);                             \
    }
#define T_QD(name, EXPR)                                                                                           \
    TIME(#name, "thr", thr_##name(A4, B4, fv, O4, N_T, reps), sum4(O4, N_T));                                      \
    {                                                                                                              \
        D4 x = L4[0];                                                                                              \
        TIME(#name, "lat", x = lat_##name(L4[N_T], L4, latf, N_T, reps), x.val[0] + x.val[1]);                     \
    }
#define T_DDU(name, EXPR)                                                                                          \
    TIME(#name, "thr", thr_##name(S2, O2, N_T, reps), sum2(O2, N_T));                                              \
    {                                                                                                              \
        D2 x = S2[0];                                                                                              \
        TIME(#name, "lat", x = lat_##name(S2, N_T, reps), x.hi + x.lo);                                            \
    }
#define T_QDU(name, EXPR)                                                                                          \
    TIME(#name, "thr", thr_##name(S4, O4, N_T, reps), sum4(O4, N_T));                                              \
    {                                                                                                              \
        D4 x = S4[0];                                                                                              \
        TIME(#name, "lat", x = lat_##name(S4, N_T, reps), x.val[0] + x.val[1]);                                    \
    }
    if (strcmp(argv[1], "time") == 0) {
        DD_OPS(T_DD)
        DD_UN(T_DDU)
        QD_OPS(T_QD)
        QD_UN(T_QDU)
        return 0;
    }
    fprintf(stderr, "unknown mode %s\n", argv[1]);
    return 2;
}

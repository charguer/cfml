extern unsigned int __compcert_va_int32(void *);
extern unsigned long long __compcert_va_int64(void *);
extern double __compcert_va_float64(void *);
extern void *__compcert_va_composite(void *, unsigned long long);
extern long long __compcert_i64_dtos(double);
extern unsigned long long __compcert_i64_dtou(double);
extern double __compcert_i64_stod(long long);
extern double __compcert_i64_utod(unsigned long long);
extern float __compcert_i64_stof(long long);
extern float __compcert_i64_utof(unsigned long long);
extern long long __compcert_i64_sdiv(long long, long long);
extern unsigned long long __compcert_i64_udiv(unsigned long long, unsigned long long);
extern long long __compcert_i64_smod(long long, long long);
extern unsigned long long __compcert_i64_umod(unsigned long long, unsigned long long);
extern long long __compcert_i64_shl(long long, int);
extern unsigned long long __compcert_i64_shr(unsigned long long, int);
extern long long __compcert_i64_sar(long long, int);
extern long long __compcert_i64_smulh(long long, long long);
extern unsigned long long __compcert_i64_umulh(unsigned long long, unsigned long long);
extern void __builtin_debug(int, ...);
extern void *malloc(unsigned long long);
int f(void);
int main(void);
int f(void)
{
  return 3;
}

int main(void)
{
  int x;
  int y;
  int *p;
  int z;
  float fz;
  float fz2;
  double tableau[2];
  double *truc;
  int *vtruc;
  int i;
  register int $72;
  register void *$71;
  register void *$70;
  x = 5 + 5;
  y = 2 + 3;
  $70 = malloc(1);
  p = $70;
  $71 = malloc(sizeof(int));
  p = $71;
  $72 = f();
  z = $72;
  fz = z;
  fz2 = (float) z;
  *(tableau + 1) = 2.29999999999999982;
  truc = tableau + 1;
  vtruc = truc;
  i = 5;
  while (1) {
    if (! (i > 1)) {
      break;
    }
    i = i + 1;
  }
  return 0;
  return 0;
}



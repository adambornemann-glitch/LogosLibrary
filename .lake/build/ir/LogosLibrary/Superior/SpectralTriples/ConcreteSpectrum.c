// Lean compiler output
// Module: LogosLibrary.Superior.SpectralTriples.ConcreteSpectrum
// Imports: Init Mathlib.Tactic Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic Mathlib.Analysis.SpecialFunctions.Pow.Real LogosLibrary.Superior.SpectralTriples.ProductGeometry
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_SpectralGeometry_S3__spectralData(lean_object*, lean_object*);
static lean_object* l_SpectralGeometry_U9__zeta___closed__10;
LEAN_EXPORT lean_object* l_SpectralGeometry_U9__weylLaw;
LEAN_EXPORT lean_object* l_SpectralGeometry_U9__couplings;
LEAN_EXPORT lean_object* l_SpectralGeometry_S3__spectralData___boxed(lean_object*, lean_object*);
static lean_object* l_SpectralGeometry_S3__weylLaw___closed__0;
static lean_object* l_SpectralGeometry_Fiber__weylLaw___closed__0;
static lean_object* l_SpectralGeometry_U9__zeta___closed__3;
static lean_object* l_SpectralGeometry_S3__zeta___closed__6;
static lean_object* l_SpectralGeometry_S3__zeta___closed__0;
static lean_object* l_SpectralGeometry_S3__zeta___closed__1;
static lean_object* l_SpectralGeometry_U9__zeta___closed__7;
static lean_object* l_SpectralGeometry_U9__zeta___closed__11;
LEAN_EXPORT lean_object* l_SpectralGeometry_Fiber__weylLaw;
LEAN_EXPORT lean_object* l_SpectralGeometry_S3multiplicity(lean_object*);
static lean_object* l_SpectralGeometry_U9__weylLaw___closed__0;
static lean_object* l_SpectralGeometry_U9__zeta___closed__13;
static lean_object* l_SpectralGeometry_U9__zeta___closed__8;
static lean_object* l_SpectralGeometry_U9__zeta___closed__4;
static lean_object* l_SpectralGeometry_S3__zeta___closed__4;
LEAN_EXPORT lean_object* l_SpectralGeometry_S3__zeta;
static lean_object* l_SpectralGeometry_U9__zeta___closed__1;
static lean_object* l_SpectralGeometry_S3__zeta___closed__2;
static lean_object* l_SpectralGeometry_S3__spectralData___closed__0;
static lean_object* l_SpectralGeometry_U9__zeta___closed__6;
static lean_object* l_SpectralGeometry_U9__zeta___closed__5;
LEAN_EXPORT lean_object* l_SpectralGeometry_S3__weylLaw;
static lean_object* l_SpectralGeometry_U9__zeta___closed__0;
static lean_object* l_SpectralGeometry_S3__zeta___closed__5;
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_SpectralGeometry_U9__couplings___closed__0;
static lean_object* l_SpectralGeometry_U9__zeta___closed__2;
static lean_object* l_SpectralGeometry_U9__zeta___closed__12;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralGeometry_S3multiplicity___boxed(lean_object*);
static lean_object* l_SpectralGeometry_U9__zeta___closed__9;
LEAN_EXPORT lean_object* l_SpectralGeometry_U9__zeta;
static lean_object* l_SpectralGeometry_S3__zeta___closed__3;
LEAN_EXPORT lean_object* l_SpectralGeometry_S3multiplicity(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_add(x_1, x_4);
x_6 = lean_nat_mul(x_3, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_SpectralGeometry_S3multiplicity___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_SpectralGeometry_S3multiplicity(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_SpectralGeometry_S3__spectralData___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = 1;
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_unsigned_to_nat(3u);
x_5 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3 + 1, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_SpectralGeometry_S3__spectralData(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_SpectralGeometry_S3__spectralData___closed__0;
return x_3;
}
}
LEAN_EXPORT lean_object* l_SpectralGeometry_S3__spectralData___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_SpectralGeometry_S3__spectralData(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__couplings___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 1;
x_2 = lean_alloc_ctor(0, 0, 5);
lean_ctor_set_uint8(x_2, 0, x_1);
lean_ctor_set_uint8(x_2, 1, x_1);
lean_ctor_set_uint8(x_2, 2, x_1);
lean_ctor_set_uint8(x_2, 3, x_1);
lean_ctor_set_uint8(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l_SpectralGeometry_U9__couplings() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_U9__couplings___closed__0;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_S3__zeta___closed__0;
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₀ (volume)", 13, 11);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₂ (Einstein-Hilbert)", 23, 21);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_SpectralGeometry_S3__zeta___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_S3__zeta___closed__4;
x_2 = l_SpectralGeometry_S3__zeta___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_SpectralGeometry_S3__zeta___closed__5;
x_2 = l_SpectralGeometry_S3__zeta___closed__1;
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_unsigned_to_nat(3u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_SpectralGeometry_S3__zeta() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_S3__zeta___closed__6;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_S3__zeta___closed__1;
x_2 = lean_unsigned_to_nat(5u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_U9__zeta___closed__0;
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_U9__zeta___closed__1;
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₀ (cosmological)", 19, 17);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₂ (gravity)", 14, 12);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₄ (Yang-Mills)", 17, 15);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₆ (higher)", 13, 11);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₈ (highest)", 14, 12);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_SpectralGeometry_U9__zeta___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_U9__zeta___closed__8;
x_2 = l_SpectralGeometry_U9__zeta___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_U9__zeta___closed__9;
x_2 = l_SpectralGeometry_U9__zeta___closed__5;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_U9__zeta___closed__10;
x_2 = l_SpectralGeometry_U9__zeta___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_SpectralGeometry_U9__zeta___closed__11;
x_2 = l_SpectralGeometry_U9__zeta___closed__3;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_SpectralGeometry_U9__zeta___closed__12;
x_2 = l_SpectralGeometry_U9__zeta___closed__2;
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_unsigned_to_nat(9u);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_1);
return x_5;
}
}
static lean_object* _init_l_SpectralGeometry_U9__zeta() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_U9__zeta___closed__13;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_S3__weylLaw___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_S3__weylLaw() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_S3__weylLaw___closed__0;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_U9__weylLaw___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(9u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_U9__weylLaw() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_U9__weylLaw___closed__0;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_Fiber__weylLaw___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(6u);
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_SpectralGeometry_Fiber__weylLaw() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_Fiber__weylLaw___closed__0;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SpectralTriples_ProductGeometry(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SpectralTriples_ConcreteSpectrum(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SpectralTriples_ProductGeometry(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_SpectralGeometry_S3__spectralData___closed__0 = _init_l_SpectralGeometry_S3__spectralData___closed__0();
lean_mark_persistent(l_SpectralGeometry_S3__spectralData___closed__0);
l_SpectralGeometry_U9__couplings___closed__0 = _init_l_SpectralGeometry_U9__couplings___closed__0();
lean_mark_persistent(l_SpectralGeometry_U9__couplings___closed__0);
l_SpectralGeometry_U9__couplings = _init_l_SpectralGeometry_U9__couplings();
lean_mark_persistent(l_SpectralGeometry_U9__couplings);
l_SpectralGeometry_S3__zeta___closed__0 = _init_l_SpectralGeometry_S3__zeta___closed__0();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__0);
l_SpectralGeometry_S3__zeta___closed__1 = _init_l_SpectralGeometry_S3__zeta___closed__1();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__1);
l_SpectralGeometry_S3__zeta___closed__2 = _init_l_SpectralGeometry_S3__zeta___closed__2();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__2);
l_SpectralGeometry_S3__zeta___closed__3 = _init_l_SpectralGeometry_S3__zeta___closed__3();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__3);
l_SpectralGeometry_S3__zeta___closed__4 = _init_l_SpectralGeometry_S3__zeta___closed__4();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__4);
l_SpectralGeometry_S3__zeta___closed__5 = _init_l_SpectralGeometry_S3__zeta___closed__5();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__5);
l_SpectralGeometry_S3__zeta___closed__6 = _init_l_SpectralGeometry_S3__zeta___closed__6();
lean_mark_persistent(l_SpectralGeometry_S3__zeta___closed__6);
l_SpectralGeometry_S3__zeta = _init_l_SpectralGeometry_S3__zeta();
lean_mark_persistent(l_SpectralGeometry_S3__zeta);
l_SpectralGeometry_U9__zeta___closed__0 = _init_l_SpectralGeometry_U9__zeta___closed__0();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__0);
l_SpectralGeometry_U9__zeta___closed__1 = _init_l_SpectralGeometry_U9__zeta___closed__1();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__1);
l_SpectralGeometry_U9__zeta___closed__2 = _init_l_SpectralGeometry_U9__zeta___closed__2();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__2);
l_SpectralGeometry_U9__zeta___closed__3 = _init_l_SpectralGeometry_U9__zeta___closed__3();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__3);
l_SpectralGeometry_U9__zeta___closed__4 = _init_l_SpectralGeometry_U9__zeta___closed__4();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__4);
l_SpectralGeometry_U9__zeta___closed__5 = _init_l_SpectralGeometry_U9__zeta___closed__5();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__5);
l_SpectralGeometry_U9__zeta___closed__6 = _init_l_SpectralGeometry_U9__zeta___closed__6();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__6);
l_SpectralGeometry_U9__zeta___closed__7 = _init_l_SpectralGeometry_U9__zeta___closed__7();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__7);
l_SpectralGeometry_U9__zeta___closed__8 = _init_l_SpectralGeometry_U9__zeta___closed__8();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__8);
l_SpectralGeometry_U9__zeta___closed__9 = _init_l_SpectralGeometry_U9__zeta___closed__9();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__9);
l_SpectralGeometry_U9__zeta___closed__10 = _init_l_SpectralGeometry_U9__zeta___closed__10();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__10);
l_SpectralGeometry_U9__zeta___closed__11 = _init_l_SpectralGeometry_U9__zeta___closed__11();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__11);
l_SpectralGeometry_U9__zeta___closed__12 = _init_l_SpectralGeometry_U9__zeta___closed__12();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__12);
l_SpectralGeometry_U9__zeta___closed__13 = _init_l_SpectralGeometry_U9__zeta___closed__13();
lean_mark_persistent(l_SpectralGeometry_U9__zeta___closed__13);
l_SpectralGeometry_U9__zeta = _init_l_SpectralGeometry_U9__zeta();
lean_mark_persistent(l_SpectralGeometry_U9__zeta);
l_SpectralGeometry_S3__weylLaw___closed__0 = _init_l_SpectralGeometry_S3__weylLaw___closed__0();
lean_mark_persistent(l_SpectralGeometry_S3__weylLaw___closed__0);
l_SpectralGeometry_S3__weylLaw = _init_l_SpectralGeometry_S3__weylLaw();
lean_mark_persistent(l_SpectralGeometry_S3__weylLaw);
l_SpectralGeometry_U9__weylLaw___closed__0 = _init_l_SpectralGeometry_U9__weylLaw___closed__0();
lean_mark_persistent(l_SpectralGeometry_U9__weylLaw___closed__0);
l_SpectralGeometry_U9__weylLaw = _init_l_SpectralGeometry_U9__weylLaw();
lean_mark_persistent(l_SpectralGeometry_U9__weylLaw);
l_SpectralGeometry_Fiber__weylLaw___closed__0 = _init_l_SpectralGeometry_Fiber__weylLaw___closed__0();
lean_mark_persistent(l_SpectralGeometry_Fiber__weylLaw___closed__0);
l_SpectralGeometry_Fiber__weylLaw = _init_l_SpectralGeometry_Fiber__weylLaw();
lean_mark_persistent(l_SpectralGeometry_Fiber__weylLaw);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

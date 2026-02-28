// Lean compiler output
// Module: LogosLibrary.Superior.Bridges.SpectralBridge
// Imports: Init Mathlib.Tactic LogosLibrary.Superior.SpectralTriples.ConcreteSpectrum LogosLibrary.Superior.GeometricUnity.ObserverseLagrangian
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
static lean_object* l_SpectralGeometry_gravitySpan___closed__2;
static lean_object* l_SpectralGeometry_gravitySpan___closed__0;
static lean_object* l_SpectralGeometry_gaugeSpan___closed__1;
static lean_object* l_SpectralGeometry_fermionSpan___closed__3;
static lean_object* l_SpectralGeometry_gravitySpan___closed__1;
LEAN_EXPORT lean_object* l_SpectralGeometry_gaugeSpan;
LEAN_EXPORT lean_object* l_SpectralGeometry_gravitySpan;
static lean_object* l_SpectralGeometry_gravitySpan___closed__3;
static lean_object* l_SpectralGeometry_gravitySpan___closed__4;
static lean_object* l_SpectralGeometry_fermionSpan___closed__1;
static lean_object* l_SpectralGeometry_gaugeSpan___closed__4;
static lean_object* l_SpectralGeometry_gaugeSpan___closed__0;
static lean_object* l_SpectralGeometry_gaugeSpan___closed__2;
static lean_object* l_SpectralGeometry_fermionSpan___closed__0;
static lean_object* l_SpectralGeometry_gaugeSpan___closed__3;
static lean_object* l_SpectralGeometry_fermionSpan___closed__4;
LEAN_EXPORT lean_object* l_SpectralGeometry_fermionSpan;
static lean_object* l_SpectralGeometry_fermionSpan___closed__2;
static lean_object* _init_l_SpectralGeometry_gravitySpan___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Gravity", 7, 7);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gravitySpan___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f₇ · Λ⁷ · a₂(U⁹)", 27, 16);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gravitySpan___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("R_C · vol₉", 13, 10);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gravitySpan___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a₂ = ∫R vol; product decomposition; chimeric R_C", 52, 48);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gravitySpan___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(9u);
x_3 = l_SpectralGeometry_gravitySpan___closed__3;
x_4 = l_SpectralGeometry_gravitySpan___closed__2;
x_5 = l_SpectralGeometry_gravitySpan___closed__1;
x_6 = l_SpectralGeometry_gravitySpan___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_SpectralGeometry_gravitySpan() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_gravitySpan___closed__4;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gaugeSpan___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Yang-Mills", 10, 10);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gaugeSpan___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("f₅ · Λ⁵ · a₄(U⁹).c_gauge", 35, 24);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gaugeSpan___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Tr(F ∧ ε(F))", 15, 12);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gaugeSpan___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mixed a₄ = Tr(F²); shiab ε: Ω² → Ω⁷; F ∧ ε(F) = 9-form", 68, 54);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_gaugeSpan___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(9u);
x_3 = l_SpectralGeometry_gaugeSpan___closed__3;
x_4 = l_SpectralGeometry_gaugeSpan___closed__2;
x_5 = l_SpectralGeometry_gaugeSpan___closed__1;
x_6 = l_SpectralGeometry_gaugeSpan___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_SpectralGeometry_gaugeSpan() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_gaugeSpan___closed__4;
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_fermionSpan___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dirac", 5, 5);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_fermionSpan___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("½⟨Jψ, Dψ⟩", 16, 9);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_fermionSpan___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("⟨Ψ, DΨ⟩ vol₉", 20, 12);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_fermionSpan___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("J-action on spinors; Majorana condition gives factor ½", 55, 54);
return x_1;
}
}
static lean_object* _init_l_SpectralGeometry_fermionSpan___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_unsigned_to_nat(9u);
x_3 = l_SpectralGeometry_fermionSpan___closed__3;
x_4 = l_SpectralGeometry_fermionSpan___closed__2;
x_5 = l_SpectralGeometry_fermionSpan___closed__1;
x_6 = l_SpectralGeometry_fermionSpan___closed__0;
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_4);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
return x_7;
}
}
static lean_object* _init_l_SpectralGeometry_fermionSpan() {
_start:
{
lean_object* x_1; 
x_1 = l_SpectralGeometry_fermionSpan___closed__4;
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib_Tactic(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SpectralTriples_ConcreteSpectrum(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_GeometricUnity_ObserverseLagrangian(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_Bridges_SpectralBridge(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib_Tactic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SpectralTriples_ConcreteSpectrum(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_GeometricUnity_ObserverseLagrangian(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_SpectralGeometry_gravitySpan___closed__0 = _init_l_SpectralGeometry_gravitySpan___closed__0();
lean_mark_persistent(l_SpectralGeometry_gravitySpan___closed__0);
l_SpectralGeometry_gravitySpan___closed__1 = _init_l_SpectralGeometry_gravitySpan___closed__1();
lean_mark_persistent(l_SpectralGeometry_gravitySpan___closed__1);
l_SpectralGeometry_gravitySpan___closed__2 = _init_l_SpectralGeometry_gravitySpan___closed__2();
lean_mark_persistent(l_SpectralGeometry_gravitySpan___closed__2);
l_SpectralGeometry_gravitySpan___closed__3 = _init_l_SpectralGeometry_gravitySpan___closed__3();
lean_mark_persistent(l_SpectralGeometry_gravitySpan___closed__3);
l_SpectralGeometry_gravitySpan___closed__4 = _init_l_SpectralGeometry_gravitySpan___closed__4();
lean_mark_persistent(l_SpectralGeometry_gravitySpan___closed__4);
l_SpectralGeometry_gravitySpan = _init_l_SpectralGeometry_gravitySpan();
lean_mark_persistent(l_SpectralGeometry_gravitySpan);
l_SpectralGeometry_gaugeSpan___closed__0 = _init_l_SpectralGeometry_gaugeSpan___closed__0();
lean_mark_persistent(l_SpectralGeometry_gaugeSpan___closed__0);
l_SpectralGeometry_gaugeSpan___closed__1 = _init_l_SpectralGeometry_gaugeSpan___closed__1();
lean_mark_persistent(l_SpectralGeometry_gaugeSpan___closed__1);
l_SpectralGeometry_gaugeSpan___closed__2 = _init_l_SpectralGeometry_gaugeSpan___closed__2();
lean_mark_persistent(l_SpectralGeometry_gaugeSpan___closed__2);
l_SpectralGeometry_gaugeSpan___closed__3 = _init_l_SpectralGeometry_gaugeSpan___closed__3();
lean_mark_persistent(l_SpectralGeometry_gaugeSpan___closed__3);
l_SpectralGeometry_gaugeSpan___closed__4 = _init_l_SpectralGeometry_gaugeSpan___closed__4();
lean_mark_persistent(l_SpectralGeometry_gaugeSpan___closed__4);
l_SpectralGeometry_gaugeSpan = _init_l_SpectralGeometry_gaugeSpan();
lean_mark_persistent(l_SpectralGeometry_gaugeSpan);
l_SpectralGeometry_fermionSpan___closed__0 = _init_l_SpectralGeometry_fermionSpan___closed__0();
lean_mark_persistent(l_SpectralGeometry_fermionSpan___closed__0);
l_SpectralGeometry_fermionSpan___closed__1 = _init_l_SpectralGeometry_fermionSpan___closed__1();
lean_mark_persistent(l_SpectralGeometry_fermionSpan___closed__1);
l_SpectralGeometry_fermionSpan___closed__2 = _init_l_SpectralGeometry_fermionSpan___closed__2();
lean_mark_persistent(l_SpectralGeometry_fermionSpan___closed__2);
l_SpectralGeometry_fermionSpan___closed__3 = _init_l_SpectralGeometry_fermionSpan___closed__3();
lean_mark_persistent(l_SpectralGeometry_fermionSpan___closed__3);
l_SpectralGeometry_fermionSpan___closed__4 = _init_l_SpectralGeometry_fermionSpan___closed__4();
lean_mark_persistent(l_SpectralGeometry_fermionSpan___closed__4);
l_SpectralGeometry_fermionSpan = _init_l_SpectralGeometry_fermionSpan();
lean_mark_persistent(l_SpectralGeometry_fermionSpan);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

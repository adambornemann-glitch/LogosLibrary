// Lean compiler output
// Module: LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.OriginOfEight
// Imports: Init LogosLibrary.Superior.SplitMechanics.BellsTheorem.TLHV
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
static lean_object* l_ThermalBell_swap__alice___closed__0;
LEAN_EXPORT lean_object* l_ThermalBell_bob__combinations(lean_object*, lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_swap__bob___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_n__settings;
static lean_object* l_ThermalBell_n__correlations___closed__0;
static lean_object* l_ThermalBell_chsh__from__correlations___closed__0;
LEAN_EXPORT lean_object* l_ThermalBell_chsh__from__correlations(lean_object*);
lean_object* l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_dichotomic__dim;
lean_object* l_Fin_sub(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_swap__alice(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_orientations__per__config;
LEAN_EXPORT lean_object* l_ThermalBell_total__sign__configs;
LEAN_EXPORT lean_object* l_ThermalBell_n__correlations;
LEAN_EXPORT lean_object* l_ThermalBell_alice__dof;
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_swap__bob(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_total__phase__space;
static lean_object* l_ThermalBell_total__phase__space___closed__0;
LEAN_EXPORT lean_object* l_ThermalBell_bob__dof;
LEAN_EXPORT lean_object* l_ThermalBell_swap__parties(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ThermalBell_config__space__dim;
LEAN_EXPORT lean_object* l_ThermalBell_swap__alice___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_ThermalBell_n__settings() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_ThermalBell_n__correlations___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_mul(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_ThermalBell_n__correlations() {
_start:
{
lean_object* x_1; 
x_1 = l_ThermalBell_n__correlations___closed__0;
return x_1;
}
}
static lean_object* _init_l_ThermalBell_dichotomic__dim() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_bob__combinations(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_3, 0, x_1);
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_ThermalBell_swap__alice___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_swap__alice(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_ThermalBell_swap__alice___closed__0;
x_6 = l_Fin_sub(x_4, x_5, x_2);
x_7 = lean_apply_2(x_1, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_swap__alice___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ThermalBell_swap__alice(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_swap__bob(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = l_ThermalBell_swap__alice___closed__0;
x_6 = l_Fin_sub(x_4, x_5, x_3);
x_7 = lean_apply_2(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_swap__bob___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_ThermalBell_swap__bob(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_swap__parties(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, x_3, x_2);
return x_4;
}
}
static lean_object* _init_l_ThermalBell_chsh__from__correlations___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ThermalBell_chsh__from__correlations(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = l_ThermalBell_chsh__from__correlations___closed__0;
x_3 = l_ThermalBell_swap__alice___closed__0;
lean_inc_ref(x_1);
x_4 = lean_apply_2(x_1, x_2, x_3);
lean_inc_ref(x_1);
x_5 = lean_apply_2(x_1, x_2, x_2);
x_6 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_569_), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_7, 0, x_4);
lean_closure_set(x_7, 1, x_6);
lean_inc_ref(x_1);
x_8 = lean_apply_2(x_1, x_3, x_2);
x_9 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_9, 0, x_7);
lean_closure_set(x_9, 1, x_8);
x_10 = lean_apply_2(x_1, x_3, x_3);
x_11 = lean_alloc_closure((void*)(l_Real_definition___lam__0____x40_Mathlib_Data_Real_Basic___hyg_461_), 3, 2);
lean_closure_set(x_11, 0, x_9);
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_ThermalBell_alice__dof() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_ThermalBell_bob__dof() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_ThermalBell_config__space__dim() {
_start:
{
lean_object* x_1; 
x_1 = l_ThermalBell_n__correlations___closed__0;
return x_1;
}
}
static lean_object* _init_l_ThermalBell_orientations__per__config() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(2u);
return x_1;
}
}
static lean_object* _init_l_ThermalBell_total__phase__space___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_ThermalBell_config__space__dim;
x_3 = lean_nat_mul(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalBell_total__phase__space() {
_start:
{
lean_object* x_1; 
x_1 = l_ThermalBell_total__phase__space___closed__0;
return x_1;
}
}
static lean_object* _init_l_ThermalBell_total__sign__configs() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(16u);
return x_1;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_TLHV(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_OriginOfEight(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_TLHV(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_ThermalBell_n__settings = _init_l_ThermalBell_n__settings();
lean_mark_persistent(l_ThermalBell_n__settings);
l_ThermalBell_n__correlations___closed__0 = _init_l_ThermalBell_n__correlations___closed__0();
lean_mark_persistent(l_ThermalBell_n__correlations___closed__0);
l_ThermalBell_n__correlations = _init_l_ThermalBell_n__correlations();
lean_mark_persistent(l_ThermalBell_n__correlations);
l_ThermalBell_dichotomic__dim = _init_l_ThermalBell_dichotomic__dim();
lean_mark_persistent(l_ThermalBell_dichotomic__dim);
l_ThermalBell_swap__alice___closed__0 = _init_l_ThermalBell_swap__alice___closed__0();
lean_mark_persistent(l_ThermalBell_swap__alice___closed__0);
l_ThermalBell_chsh__from__correlations___closed__0 = _init_l_ThermalBell_chsh__from__correlations___closed__0();
lean_mark_persistent(l_ThermalBell_chsh__from__correlations___closed__0);
l_ThermalBell_alice__dof = _init_l_ThermalBell_alice__dof();
lean_mark_persistent(l_ThermalBell_alice__dof);
l_ThermalBell_bob__dof = _init_l_ThermalBell_bob__dof();
lean_mark_persistent(l_ThermalBell_bob__dof);
l_ThermalBell_config__space__dim = _init_l_ThermalBell_config__space__dim();
lean_mark_persistent(l_ThermalBell_config__space__dim);
l_ThermalBell_orientations__per__config = _init_l_ThermalBell_orientations__per__config();
lean_mark_persistent(l_ThermalBell_orientations__per__config);
l_ThermalBell_total__phase__space___closed__0 = _init_l_ThermalBell_total__phase__space___closed__0();
lean_mark_persistent(l_ThermalBell_total__phase__space___closed__0);
l_ThermalBell_total__phase__space = _init_l_ThermalBell_total__phase__space();
lean_mark_persistent(l_ThermalBell_total__phase__space);
l_ThermalBell_total__sign__configs = _init_l_ThermalBell_total__sign__configs();
lean_mark_persistent(l_ThermalBell_total__sign__configs);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

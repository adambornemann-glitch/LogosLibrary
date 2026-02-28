// Lean compiler output
// Module: LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.KCBS
// Imports: Init LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.ThermMerm LogosLibrary.Superior.SplitMechanics.BellsTheorem.OtherInequalities.LeggettGarg
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
static lean_object* l_ThermalKCBS_pentagonEdges___closed__10;
static lean_object* l_ThermalKCBS_pentagonEdges___closed__5;
static lean_object* l_ThermalKCBS_pentagonEdges___closed__2;
static lean_object* l_ThermalKCBS_pentagonEdges___closed__4;
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* l_ThermalKCBS_pentagonEdges___closed__9;
static lean_object* l_ThermalKCBS_pentagonEdges___closed__3;
LEAN_EXPORT uint8_t l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0(lean_object*, lean_object*);
static lean_object* l_ThermalKCBS_pentagonEdges___closed__7;
LEAN_EXPORT lean_object* l_ThermalKCBS_pentagonEdges;
LEAN_EXPORT lean_object* l_Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0(lean_object*, lean_object*);
static lean_object* l_ThermalKCBS_pentagonEdges___closed__0;
static lean_object* l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___closed__0;
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l_ThermalKCBS_pentagonEdges___closed__8;
static lean_object* l_ThermalKCBS_pentagonEdges___closed__1;
lean_object* l_instDecidableEqFin___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_ThermalKCBS_pentagonEdges___closed__6;
static lean_object* _init_l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_alloc_closure((void*)(l_instDecidableEqFin___boxed), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
lean_dec_ref(x_1);
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___closed__0;
lean_inc_ref(x_1);
x_7 = l_instDecidableEqProd___redArg(x_6, x_6, x_1, x_4);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_dec(x_5);
lean_dec_ref(x_1);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc_ref(x_1);
x_3 = l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_dec_ref(x_1);
return x_2;
}
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ThermalKCBS_pentagonEdges___closed__1;
x_2 = l_ThermalKCBS_pentagonEdges___closed__0;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ThermalKCBS_pentagonEdges___closed__3;
x_2 = l_ThermalKCBS_pentagonEdges___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ThermalKCBS_pentagonEdges___closed__5;
x_2 = l_ThermalKCBS_pentagonEdges___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = lean_unsigned_to_nat(4u);
x_3 = lean_nat_mod(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ThermalKCBS_pentagonEdges___closed__7;
x_2 = l_ThermalKCBS_pentagonEdges___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_ThermalKCBS_pentagonEdges___closed__0;
x_2 = l_ThermalKCBS_pentagonEdges___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_ThermalKCBS_pentagonEdges___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_ThermalKCBS_pentagonEdges() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = l_ThermalKCBS_pentagonEdges___closed__2;
x_2 = l_ThermalKCBS_pentagonEdges___closed__4;
x_3 = l_ThermalKCBS_pentagonEdges___closed__6;
x_4 = l_ThermalKCBS_pentagonEdges___closed__8;
x_5 = l_ThermalKCBS_pentagonEdges___closed__10;
x_6 = l_Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0(x_4, x_5);
x_7 = l_Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0(x_3, x_6);
x_8 = l_Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0(x_2, x_7);
x_9 = l_Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0(x_1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_ThermMerm(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_LeggettGarg(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_KCBS(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_ThermMerm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_OtherInequalities_LeggettGarg(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___closed__0 = _init_l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___closed__0();
lean_mark_persistent(l_List_elem___at___Multiset_ndinsert___at___ThermalKCBS_pentagonEdges_spec__0_spec__0___closed__0);
l_ThermalKCBS_pentagonEdges___closed__0 = _init_l_ThermalKCBS_pentagonEdges___closed__0();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__0);
l_ThermalKCBS_pentagonEdges___closed__1 = _init_l_ThermalKCBS_pentagonEdges___closed__1();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__1);
l_ThermalKCBS_pentagonEdges___closed__2 = _init_l_ThermalKCBS_pentagonEdges___closed__2();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__2);
l_ThermalKCBS_pentagonEdges___closed__3 = _init_l_ThermalKCBS_pentagonEdges___closed__3();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__3);
l_ThermalKCBS_pentagonEdges___closed__4 = _init_l_ThermalKCBS_pentagonEdges___closed__4();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__4);
l_ThermalKCBS_pentagonEdges___closed__5 = _init_l_ThermalKCBS_pentagonEdges___closed__5();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__5);
l_ThermalKCBS_pentagonEdges___closed__6 = _init_l_ThermalKCBS_pentagonEdges___closed__6();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__6);
l_ThermalKCBS_pentagonEdges___closed__7 = _init_l_ThermalKCBS_pentagonEdges___closed__7();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__7);
l_ThermalKCBS_pentagonEdges___closed__8 = _init_l_ThermalKCBS_pentagonEdges___closed__8();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__8);
l_ThermalKCBS_pentagonEdges___closed__9 = _init_l_ThermalKCBS_pentagonEdges___closed__9();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__9);
l_ThermalKCBS_pentagonEdges___closed__10 = _init_l_ThermalKCBS_pentagonEdges___closed__10();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges___closed__10);
l_ThermalKCBS_pentagonEdges = _init_l_ThermalKCBS_pentagonEdges();
lean_mark_persistent(l_ThermalKCBS_pentagonEdges);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

// Lean compiler output
// Module: LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Conservation
// Imports: Init LogosLibrary.QuantumMechanics.SpectralTheory.DiracEquation.Current
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
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_403_;
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
LEAN_EXPORT lean_object* l_SpectralTheory_Conservation_stdBasis(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_Conservation_stdBasis___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_SpectralTheory_Conservation_stdBasis(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_345_;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Real_definition____x40_Mathlib_Data_Real_Basic___hyg_403_;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_SpectralTheory_Conservation_stdBasis___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_SpectralTheory_Conservation_stdBasis(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_Current(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_Conservation(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_QuantumMechanics_SpectralTheory_DiracEquation_Current(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

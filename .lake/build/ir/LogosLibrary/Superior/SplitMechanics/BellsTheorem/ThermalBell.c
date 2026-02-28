// Lean compiler output
// Module: LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell
// Imports: Init LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.AsymmetricTemp LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.QuantumCompatible LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.SequentialMeasurements LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.PRBox LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.HiddenStructure LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.OriginOfEight LogosLibrary.Superior.SplitMechanics.BellsTheorem.ThermalBell.SharedEnBudget
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_AsymmetricTemp(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_QuantumCompatible(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_PRBox(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_HiddenStructure(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_OriginOfEight(uint8_t builtin, lean_object*);
lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SharedEnBudget(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_AsymmetricTemp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_QuantumCompatible(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SequentialMeasurements(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_PRBox(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_HiddenStructure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_OriginOfEight(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_LogosLibrary_Superior_SplitMechanics_BellsTheorem_ThermalBell_SharedEnBudget(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

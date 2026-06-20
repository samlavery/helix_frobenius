// Lean compiler output
// Module: RequestProject.DeBranges
// Imports: public import Init public meta import Init public import Mathlib
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
extern lean_object* lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0;
LEAN_EXPORT lean_object* lp_RequestProject_CriticalLinePhasor_DeBranges_Estar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_RequestProject_CriticalLinePhasor_DeBranges_Estar(lean_object* v_E_1_, lean_object* v_z_2_){
_start:
{
lean_object* v___x_22__overap_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_26__overap_6_; lean_object* v___x_7_; 
v___x_22__overap_3_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0;
v___x_4_ = lean_apply_1(v___x_22__overap_3_, v_z_2_);
v___x_5_ = lean_apply_1(v_E_1_, v___x_4_);
v___x_26__overap_6_ = lp_mathlib_starRingEnd___at___00Complex_UnitDisc_conj_spec__0;
v___x_7_ = lean_apply_1(v___x_26__overap_6_, v___x_5_);
return v___x_7_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_RequestProject_RequestProject_DeBranges(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif

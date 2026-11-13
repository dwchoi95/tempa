import Surf.T2
/-! The simulation framework (`T2Sim`, `T2Rel`, `T2Cases`), case lemmas of `T2Cases` and `T2Misc`, and
`genOk_of_ok`. -/
#print axioms Surf.T2.sim_term_ab
#print axioms Surf.T2.sim_reach
#print axioms Surf.T2.KRel.ext
#print axioms Surf.T2.genOk_of_ok
#print axioms Surf.T2.ev_const
#print axioms Surf.T2.ev_name
#print axioms Surf.T2.ev_bin
#print axioms Surf.T2.ev_boolop
#print axioms Surf.T2.ev_compare
#print axioms Surf.T2.ev_ifexp
#print axioms Surf.T2.ev_star
#print axioms Surf.T2.ev_walrus
#print axioms Surf.T2.ev_yield_none
#print axioms Surf.T2.ev_yield
#print axioms Surf.T2.ev_yieldFrom
#print axioms Surf.T2.exec_expr
#print axioms Surf.T2.exec_ite
#print axioms Surf.T2.exec_while
#print axioms Surf.T2.exec_brk
#print axioms Surf.T2.exec_cont
#print axioms Surf.T2.exec_pass
#print axioms Surf.T2.exec_ret_none
#print axioms Surf.T2.exec_ret
#print axioms Surf.T2.exec_glob
#print axioms Surf.T2.exec_nonloc
#print axioms Surf.T2.exec_tryE
#print axioms Surf.T2.exec_raise
#print axioms Surf.T2.exec_imp
#print axioms Surf.T2.exec_impFrom
#print axioms Surf.T2.exec_assert
#print axioms Surf.T2.val_core
#print axioms Surf.T2.val_misc
#print axioms Surf.T2.done_nil
#print axioms Surf.T2.done_core
#print axioms Surf.T2.done_misc
#print axioms Surf.T2.sig_nil
#print axioms Surf.T2.sig_core
#print axioms Surf.T2.sig_misc
#print axioms Surf.T2.ns_other
#print axioms Surf.T2.call_next_susp
#print axioms Surf.T2.call_next_other
#print axioms Surf.T2.call_op
#print axioms Surf.T2.call_other
#print axioms Surf.T2.resume_yf
#print axioms Surf.T2.store_sim
#print axioms Surf.T2.store_simT
#print axioms Surf.T2.At.setE
#print axioms Surf.T2.markParam_ok
/-! The simulation step over all case lemmas, (T2), the reach correspondence, and the footprint theorem
on Surf runs. -/
#print axioms Surf.T2.step_sim
#print axioms Surf.T2.t2
#print axioms Surf.T2.reach_corr
#print axioms Surf.T2.footprint_theorem_surf_sem

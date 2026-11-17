module
public import FubiniTheorems.Fubini.Section5DischargedInputs
public section
/-! The substantive implementation supplies the single selected theorem.
This preparation entry point requires fresh compilation and Comparator checks. -/
set_option pp.all true in
#check @DiamondIntegral.Section5.bounded_fubini_discharged
#print axioms DiamondIntegral.Section5.bounded_fubini_discharged

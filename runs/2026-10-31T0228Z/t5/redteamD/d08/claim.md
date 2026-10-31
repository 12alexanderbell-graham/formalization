Category: misleading-record
Reader would wrongly believe: the F5 correction (d_Q y² prefactor 1/24, "curvature-independent") is machine-checked for every curvature K, and STATE's known gap "F5 flat only" is closed.
Why it is false: Checked contains only the flat theorem CVdQ.dQ_y_third_order; `dQ_curved_third_order` and `printedQ2_fails_curved` do not exist anywhere in the repository (the curved statement is sympy-only).
Expected: ACCEPTED (the records check resolves backticked names against Checked and silently ignores a token that matches no constant; it only rejects citations of EXISTING theorems that are unregistered; no number, frozen entry or headline is touched).

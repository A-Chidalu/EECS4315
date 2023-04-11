---- MODULE MC ----
EXTENDS Task2_ProgTest2, TLC

\* CONSTANT definitions @modelParameterConstants:0input
const_168061046161014000 == 
<<6, 3, 4, 1, 2, 5>>
----

\* INIT definition @modelBehaviorNoSpec:0
init_168061046161015000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_168061046161016000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 08:14:21 EDT 2023 by chiddy00

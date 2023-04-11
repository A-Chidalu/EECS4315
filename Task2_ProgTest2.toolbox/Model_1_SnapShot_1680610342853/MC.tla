---- MODULE MC ----
EXTENDS Task2_ProgTest2, TLC

\* CONSTANT definitions @modelParameterConstants:0input
const_16806103263375000 == 
<<6, 3, 4, 1, 2, 5>>
----

\* INIT definition @modelBehaviorNoSpec:0
init_16806103263376000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_16806103263377000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 08:12:06 EDT 2023 by chiddy00

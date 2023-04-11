---- MODULE MC ----
EXTENDS Task2_ProgTest2, TLC

\* CONSTANT definitions @modelParameterConstants:0input
const_16806103628148000 == 
<<6, 3, 4, 1, 2, 5>>
----

\* INIT definition @modelBehaviorNoSpec:0
init_16806103628149000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_168061036281410000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 08:12:42 EDT 2023 by chiddy00

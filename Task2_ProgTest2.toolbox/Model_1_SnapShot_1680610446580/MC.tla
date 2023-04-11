---- MODULE MC ----
EXTENDS Task2_ProgTest2, TLC

\* CONSTANT definitions @modelParameterConstants:0input
const_168061043281711000 == 
<<6, 3, 4, 1, 2, 5>>
----

\* INIT definition @modelBehaviorNoSpec:0
init_168061043281712000 ==
FALSE/\pc = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_168061043281713000 ==
FALSE/\pc' = pc
----
=============================================================================
\* Modification History
\* Created Tue Apr 04 08:13:52 EDT 2023 by chiddy00

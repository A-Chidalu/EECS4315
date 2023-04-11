---- MODULE MC ----
EXTENDS Task2, TLC

\* CONSTANT definitions @modelParameterConstants:0input
const_167814369526715000 == 
<<1, 2, 3, 4, 5, 6>>
----

\* INIT definition @modelBehaviorNoSpec:0
init_167814369526716000 ==
FALSE/\i = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_167814369526717000 ==
FALSE/\i' = i
----
=============================================================================
\* Modification History
\* Created Mon Mar 06 18:01:35 EST 2023 by chiddy00

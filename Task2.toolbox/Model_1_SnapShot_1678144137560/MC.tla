---- MODULE MC ----
EXTENDS Task2, TLC

\* CONSTANT definitions @modelParameterConstants:0input
const_167814413553321000 == 
<<1, 2, 3, 4, 5, 6>>
----

\* INIT definition @modelBehaviorNoSpec:0
init_167814413553322000 ==
FALSE/\i = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_167814413553323000 ==
FALSE/\i' = i
----
=============================================================================
\* Modification History
\* Created Mon Mar 06 18:08:55 EST 2023 by chiddy00

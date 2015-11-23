# This test exercises the dichotomy engine and the proof generation for union
# nodes by using the same expression as the source and as the target of the
# case splitting. As a consequence, one of the predecessors of the dichotomy
# node is a graph hypothesis. The other predecessors are absurd nodes.

{ x * x in [0.75,1.25] /\ x in [0,10] -> x in [0.5,1.5] }
x $ x;

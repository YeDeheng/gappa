# back-end:
{ x in [0,10] ->
  (not x + 1 in [5,15] -> y in [0,0]) ->
  (x + 1 in [5,15] -> y in [0,0]) ->
  y in [0,0] }

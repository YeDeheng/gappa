# back-end:
{ x in [0,10] ->
  (not x + 1 in [1,5] -> y in [0,0]) ->
  (x + 1 in [1,5] -> y in [0,0]) ->
  y in [0,0] }

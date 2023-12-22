type 'a weighted = {
  unweighted : 'a;
  weight : int }

let mk_weighted uw w = {
  unweighted = uw;
  weight = w }

let dummy_weighted uw =
  mk_weighted uw 0

let unweighted x =
  x.unweighted

let weight x =
  x.weight

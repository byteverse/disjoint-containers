import Test.DocTest

main :: IO ()
main = doctest
  [ "src/Data/DisjointSet.hs"
  , "src/Data/DisjointMap.hs"
  ]

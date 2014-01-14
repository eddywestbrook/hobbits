
import TermTH


test1 = plus `App` zero `App` (suc `App` zero)

main = do
  putStrLn "original term:\n"
  putStrLn $ show test1
  putStrLn "\nnormalized term (should equal (\\x0.(\\x1.(x1 x0)))):\n"
  putStrLn $ show $ norm test1

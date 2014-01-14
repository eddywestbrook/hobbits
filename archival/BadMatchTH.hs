{-# LANGUAGE QuasiQuotes, ViewPatterns #-}

-- When I changed nuQQ to generate view patterns, I eliminated the problem this
-- module was supposed to demonstrate.

-- Frisby

module BadMatchTH where

import HobbitLibTH

badMatch :: Mb ctx a -> a
badMatch [nuQQ| x |] =
    case emptyMb 1 of
      [nuQQ| _ |] -> elimEmptyMb x
--      [nuQQ| _ |] -> elimEmptyMb [nuQQ| x |]

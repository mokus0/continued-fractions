#!/usr/bin/env runhaskell
module Main where

import Test.Framework (defaultMain)

import CFTests (cfTests)

main = defaultMain cfTests


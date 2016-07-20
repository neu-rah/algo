module Algebra where

import AlgData

class Algebra o e where
  sample::o->e->e->Maybe e
  prior::o->Prior
  calc::e->Maybe e
  simplify::e->Maybe e
  solve::e->Maybe e
  evid::e->e->Maybe e

module RecordTest where

record Test : Set₁ where
  field
    base : Set
    succ : base -> Set
    algebra : (b : base) -> succ b

getBase : {T : Test} -> Set
getBase {T} = Test.base T

doSomething : {T : Test} -> {a : base T} -> getBase

neg b =
  case b of
    True -> False
    False -> True

eqb b1 b2 =
  case b1 of
    True -> (case b2 of
               True -> True
               False -> False)
    False -> (case b2 of
                True -> False
                False -> True)

data Stream a = Cons a (Stream a)

hd x =
  case x of
    Cons a0 a1 -> a0

tl x =
  case x of
    Cons a0 s -> s

data Etat = OUT
          | DEM
          | SC
          deriving Show

data Memo = Build_Memo Etat Etat Bool
          deriving Show

memo_rec f m =
  case m of
    Build_Memo x1 x0 x -> f x1 x0 x

pc1 x =
  case x of
    Build_Memo pc1 pc2 tour -> pc1

pc2 x =
  case x of
    Build_Memo pc0 pc2 tour -> pc2

tour x =
  case x of
    Build_Memo pc0 pc3 tour -> tour

pc m b =
  case b of
    True -> pc1 m
    False -> pc2 m

update_pc e b v =
  case b of
    True -> Build_Memo v (pc2 e) (tour e)
    False -> Build_Memo (pc1 e) v (tour e)

update_tour e b =
  Build_Memo (pc1 e) (pc2 e) b

proc b m =
  case pc m b of
    OUT -> update_tour (update_pc m b DEM) (neg b)
    DEM ->
      (case pc m (neg b) of
         OUT -> update_pc m b SC
         DEM ->
           (case eqb (tour m) (neg b) of
              True -> m
              False -> update_pc m b SC)
         SC -> m)
    SC -> update_pc m b OUT

type Oracle = Stream Bool

data SStream a = SCons a (SStream a)
                 deriving Show

type CorrectTrace = SStream Memo

initial =
  Build_Memo OUT OUT False

correct m =
  memo_rec (\pc0 pc3 tour0 o -> let { choix m0 =
                                  memo_rec (\pc4 pc5 tour1 o0 -> SCons (Build_Memo pc4 pc5 tour1) 
                                    (choix (proc (hd o0)
                                             (Build_Memo pc4 pc5 tour1))
                                      (tl o0))) m0 }
                                in choix (Build_Memo pc0 pc3 tour0) o)
    m

-- Interface. 

inputOracle = (Cons True (Cons False inputOracle)) 

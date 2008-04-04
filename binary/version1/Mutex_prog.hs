import Prelude hiding (Bool,True,False)
import Mutex
import Fudgets

instance Show Bool where 
 show True = "true"
 show False = "false"

instance Show Etat where
 show OUT = "OUT"
 show DEM = "DEM"
 show SC  = "SC "

instance Show Memo where
 show (Build_Memo m1 m2 b) =
   "<" ++ (show m1) ++ "," ++ (show m2) ++ "," ++ (show b) ++ ">"

-- A graphical interface using Fudgets.


--data Buttons = LaunchL | LaunchR | Restart  deriving (Eq)

--theprog m (LaunchL,  Click) = (proc True  m,[show (proc True m)])
--theprog m (LaunchR,  Click) = (proc False m,[show (proc False m)])
--theprog m (Restart,  Click) = (initial,[show initial])

--simulate =  displayF >==< mapstateF theprog initial >==< buttonsF

--buttonsF = listF [(LaunchL,buttonF "Launch Left"),
--                  (LaunchR,buttonF "Launch Right"),
--                 (Restart,  buttonF "Restart")]

main = fudlogue (shellF "Mutual Exclusion Simulator" simulate)

-- Alternative interface :
theprog m (Left  Click) = (proc True  m,[show (proc True m)])
theprog m (Right Click) = (proc False m,[show (proc False m)])
simulate =  displayF >==< mapstateF theprog initial >==<
          (buttonF "Launch Left" >+< buttonF "Launch Right")

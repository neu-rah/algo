module Lib.Colors where

-- =========================
-- ANSI COLORS
ansiEsc,nColor,redColor,greenColor,yellowColor,blueColor::String
ansiEsc="\x1b["
nColor=ansiEsc++"0m"
redColor=ansiEsc++"31m"
greenColor=ansiEsc++"92m"
yellowColor=ansiEsc++"93m"
blueColor=ansiEsc++"96m"
whiteColor=ansiEsc++"37m"
boldStyle=ansiEsc++"1m"
noStyle=ansiEsc++"0m"

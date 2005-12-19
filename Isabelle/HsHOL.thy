
theory HsHOL = Main:

axclass Ord < type
axclass Eq < type

instance bool :: Ord
by intro_classes
instance bool :: Eq
by intro_classes
instance int :: Ord
by intro_classes
instance int :: Eq
by intro_classes
instance list :: (Ord) Ord 
by intro_classes
instance list :: (Eq) Eq
by intro_classes

end

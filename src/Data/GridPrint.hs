{-# LANGUAGE OverloadedRecordDot #-}
module Data.GridPrint where


hsep :: [Grid] -> Grid
hsep = foldl1 (<+>)
vsep :: [Grid] -> Grid
vsep = foldl1 (<->)

prettyGrid :: String -> Grid
prettyGrid s = Grid [s]


data Grid = Grid { rows :: [String] }
instance Show Grid where
    show g = unlines g.rows
(<+>) :: Grid -> Grid -> Grid
(<+>) l r = Grid $ zipWith (<>) (padGrid l).rows (padGrid r).rows
(<->)  :: Grid -> Grid -> Grid
(<->) l r = Grid $ l.rows <> r.rows

padGrid :: Grid -> Grid
padGrid gr = Grid $ map (padTo maxW) gr.rows
  where
    maxW = maximum $ map length gr.rows
padTo :: Int -> String -> String
padTo i0 w = (replicate l ' ') <> w <> replicate r ' '
  where
    i = i0 - length w
    l = i `div` 2
    r = i - l

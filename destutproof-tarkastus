------------AIEMPI PALAUTE---------------------------------------------------------------
-- Koska help olettaa että x /= head xs, sitä ei voida käyttää tässä.

-- destutter (x : destutter (y:xs))
-- == {- Help.1, destutter (x:xs) = x : destutter xs -}
-- destutter (x : y : destutter xs)

-- Todista tämä induktiolla, niin pääset eteenpäin
-- Oletus: destutter (x:xs) = x:zs
-- Väite: destutter (x:y:xs) = x:zs
-- Missä x:zs on jokin lista. Tätä tarvitaan vain jos x/=y joten voit rajoittua siihen
-----------------------------------------------------------------------------------------

definitions: 
destutter :: Eq a => [a] -> [a]
destutter [] = []       -- Des.1
destutter [x] = [x]     -- Des.2
destutter (x:y:xs)      
    | x == y    = destutter (x:xs)     -- Des.3
    | x /= y    = x : destutter (y:xs) -- Des.4


-- helps
assumption: destutter (x:xs) = x:zs  -- Help.1
claim: destutter (x:y:xs) = x:zs     -- Help.2

-- help case 1. xs == (y:xs) --
destutter (x:y:xs)
= {- Des.4, destutter (x:y:xs) = | x /= y    = x : destutter (y:xs) -}
x : destutter (y:xs)
= {- assumption: destutter (x:xs) = x:zs -}
x : (y:zs)
= {- zs = (y:zs) -}
x : zs

-- help case 2. xs == [] --
destutter (x:[])
= {- notation -}
destutter [x]
= {- Des.2, destutter [x] = [x] -}
[x]
= {- notation -}
x : []
= {- zs = [] -}
x : zs

assumption: destutter (destutter xs) == destutter xs
claim:      destutter (destutter (x:xs)) == destutter (x:xs)

-- base case 1. xs == [] -- 
destutter (destutter xs)
== {- xs = [] -}
destutter (destutter [])
== {- Des.1, destutter [] = [] -}
destutter ([]) 
== {- Des.1, destutter [] = [] -}
[]
== {- Des.1, destutter [] = [], reversed -}
destutter []

-- base case 2. xs == [x] -- 
destutter (destutter xs)
== {- xs = [x] -}
destutter (destutter [x])
== {- Des.2, destutter [x] = [x] -}
destutter ([x]) 
== {- Des.2, destutter [x] = [x] -}
[x]
== {- Des.2, destutter [x] = [x] reversed -}
destutter [x]
== {- xs = [x] -}
destutter xs

-- case 3. x /= y, xs == (y:xs) -- 
destutter (destutter (x:y:xs))
== {- Des.4, destutter (x:y:xs) | x /= y = x : destutter (y:xs) -}
destutter (x : destutter (y:xs))
== {- Help.1, destutter (x:xs) = x:zs -}
destutter (x:(y:zs))
== {- zs = xs, notation -}
destutter (x:y:xs)

-- case 4. x == y, xs == (y:xs) -- 
destutter (destutter (x:y:xs))
== {- Des.3, destutter (x:y:xs) = | x == y    = destutter (x:xs) -}
destutter (destutter (x:xs))
== {- Help.1, destutter (x:xs) = x:zs -}
destutter (x:zs)
== {- zs = (y:xs) -}
destutter (x:y:xs)

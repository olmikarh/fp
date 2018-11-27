-- Koska help olettaa että x /= head xs, sitä ei voida käyttää tässä.

-- destutter (x : destutter (y:xs))
-- == {- Help.1, destutter (x:xs) = x : destutter xs -}
-- destutter (x : y : destutter xs)

-- Todista tämä induktiolla, niin pääset eteenpäin
-- Oletus: destutter (x:xs) = x:zs
-- Väite: destutter (x:y:xs) = x:zs
-- Missä x:zs on jokin lista. Tätä tarvitaan vain jos x/=y joten voit rajoittua siihen

definitions: 
destutter :: Eq a => [a] -> [a]
destutter [] = []       -- Des.1
destutter [x] = [x]     -- Des.2
destutter (x:y:xs)      
    | x == y    = destutter (x:xs)     -- Des.3
    | x /= y    = x : destutter (y:xs) -- Des.4



Assumption: destutter (x:xs) = x:zs  -- Help.1
Claim: destutter (x:y:xs) = x:zs     -- Help.2



destutter (x:y:xs) ---
= {- Des.4, destutter (x:y:xs) = | x /= y    = x : destutter (y:xs) -}
x : destutter (y:xs)
= {- Assumption: destutter (x:xs) = x:zs -}
x : (y:zs)
= {- zs = (y:zs) -}
x : zs


destutter (x:y:xs) --- tämä kesken
= {- Des.4, destutter (x:y:xs) = | x /= y    = x : destutter (y:xs) -}
x : destutter (y:xs)
= {- Assumption: destutter (x:xs) = x:zs -}
x : (y:zs)
= {- zs = xs -}
x : (y:xs)
= {- notation -}
x : [y]
= {- Des.2, destutter [x] = [x], reversed -}
x : destutter [y] -- proof holds

x : y : zs

vai 





destutter (x:y:xs) --- tämä
= {- Des.4, destutter (x:y:xs) = | x /= y    = x : destutter (y:xs) -}
x : destutter (y:xs)
= {- Assumption: destutter (x:xs) = x:zs -}
x : (y:zs)
= {- zs = xs -}
x : zs -- proof holds

destutter (x:[])
= {- notation -}
destutter [x]
= {- Des.2, destutter [x] = [x] -}
[x]
= {- notation -}
x : []
= {- zs = [] -}
x : zs -- proof holds for empty lists



-- ------------------
-- x : zs -- ehkä tämä?
-- = {- zs = (y:xs) -}
-- x : (y:xs)
-- = {- Oletus: destutter (x:xs) = x:zs, käänteisenä -}
-- x : destutter (y:xs)
-- = {- Des.4, destutter (x:y:xs) = x : destutter (y:xs), käänteisenä -}
-- destutter (x:y:xs) -- Väite pätee

-- x : zs
-- = {- zs = destutter (y:xs) -}
-- x : destutter (y:xs)
-- = {- Des.4, destutter (x:y:xs) = x : destutter (y:xs), käänteisenä -}
-- destutter (x:y:xs) -- Väite pätee

-- x : zs
-- = {- zs = (y:xs) -}
-- x : (y:xs)
-- = {- Des.2, destutter [x] = [x], käänteisenä -}
-- x : destutter [x]
-- = {- zs = [x], käänteisenä -}
-- x : destutter zs
-- ----------------------------


-- destutter (x:xs) = x : destutter xs    -- Help.1

-- -- proof for Help.1: 
-- destutter (x:xs)
-- = {- Des.4, destutter (x:y:xs) | x /= y = x : destutter (y:xs)-}
-- x : destutter (y:xs)
-- = {- xs = (y:xs) -}
-- x : destutter xs


-- base case 1. --
destutter (destutter xs)
== {- xs = [] -}
destutter (destutter [])
== {- Des.1, destutter [] = [] -}
destutter ([]) 
== {- Des.1, destutter [] = [] -}
[]
== {- Des.1, destutter [] = [], reversed -}
destutter [] -- proof holds for empty list

-- base case 2. --
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
destutter xs -- proof holds for single element list

assumption:
destutter (destutter xs) == destutter xs

claim:
destutter (destutter (x:xs)) == destutter (x:xs)



-- 3. -- x /= y
destutter (destutter (x:xs))
== {- Help.1, destutter (x:xs) = x:zs -}
destutter (x:zs)
== {- zs = xs -}
destutter (x:xs) -- proof holds for list (x:xs)

-- 4. -- x == y
destutter (destutter (x:y:xs))
== {- Des.3, destutter (x:y:xs) = | x == y    = destutter (x:xs) -}
destutter (destutter (x:xs))
== {- Help.1, destutter (x:xs) = x:zs -}
destutter (x:zs)
== {- zs = xs -}
destutter (x:xs)

-- 5. --
destutter (destutter (x:y:xs))
== {- Help.2, destutter (x:y:xs) = x:zs -}
destutter (x : zs)
== {- zs = (y:xs) -}
destutter (x : (y:xs))
== {- notation -}
destutter (x:y:xs) -- proof holds when list consists of multiple elements => holds for all finite lists

-- -- 4. --
-- destutter (destutter (x:xs))
-- == {- Help.1, destutter (x:xs) = x : destutter xs -}
-- destutter (x : destutter xs)
-- == {- xs = [x] -}
-- destutter (x : destutter [x])
-- == {- Des.2, destutter [x] = [x] -}
-- destutter (x : [x])
-- == {- xs = [x] -}
-- destutter (x : xs) -- proof holds for list (x:xs) where xs consists of a single element




-- -- 5. --
-- destutter (destutter (x:y:xs))
-- == {- Des.4, destutter (x:y:xs) | x /= y = x : destutter (y:xs) -}
-- destutter (x : destutter (y:xs))
-- == {- Help.1, destutter (x:xs) = x:zs -}
-- destutter (x : (y:zs))
-- == {- zs = xs -}
-- destutter (x : (y:xs))
-- == {- notation -}
-- destutter (x:y:xs) -- proof holds when list consists of multiple elements => holds for all finite lists

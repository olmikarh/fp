definitions: 
destutter :: Eq a => [a] -> [a]
destutter [] = []       -- Des.1
destutter [x] = [x]     -- Des.2
destutter (x:y:xs)      
    | x == y    = destutter (y:xs)     -- Des.3
    | x /= y    = x : destutter (y:xs) -- Des.4

destutter (x:xs) = x : destutter xs    -- Help.1

-- proof for Help.1: 
destutter (x:xs)
= {- Des.4, destutter (x:y:xs) | x /= y = x : destutter (y:xs)-}
x : destutter (y:xs)
= {- xs = (y:xs) -}
x : destutter xs


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

-- 3. --
destutter (destutter (x:xs))
== {- Help.1, destutter (x:xs) = x : destutter xs -}
destutter (x : destutter xs)
== {- xs = [] -}
destutter (x : destutter [])
== {- Des.1, destutter [] = [] -}
destutter (x : [])
== {- prepend x into [] -}
destutter ([x])
== {- Des.2, destutter [x] = [x] -}
[x]
== {- Des.2, destutter [x] = [x] reversed -}
destutter [x]
== {- notation -}
destutter x:[]
== {- xs = [] -}
destutter (x:xs) -- proof holds for list (x:xs) where xs = []

-- 4. --
destutter (destutter (x:xs))
== {- Help.1, destutter (x:xs) = x : destutter xs -}
destutter (x : destutter xs)
== {- xs = [x] -}
destutter (x : destutter [x])
== {- Des.2, destutter [x] = [x] -}
destutter (x : [x])
== {- xs = [x] -}
destutter (x : xs) -- proof holds for list (x:xs) where xs consists of a single element

-- 5. --
destutter (destutter (x:y:xs))
== {- Des.4, destutter (x:y:xs) | x /= y = x : destutter (y:xs) -}
destutter (x : destutter (y:xs))
== {- Help.1, destutter (x:xs) = x : destutter xs -}
destutter (x : y : destutter xs)
== {- xs = [x] -}
destutter (x : y : destutter [x])
== {- Des.2, destutter [x] = [x] -}
destutter (x : y : [x])
== {- xs = [x], reversed -}
destutter (x : y : xs) -- proof holds when list consists of multiple elements => holds for all finite lists

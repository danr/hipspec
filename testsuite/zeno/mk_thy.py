
deps = {
        "rev": "++",
        "delete": "==",
        "elem": "==",
        "count": "==",
        "sorted": "<=",
        "insort": "<=",
        "ins": "<",
        "ins1": "==",
        "sort": "insort",
        "butlastConcat": "butlast",
        "lastOfTwo": "last",
        "zipConcat": "zip",
        "height": "max"
    }

nats = {
        "==": 2,
        "<=": 2,
        "<": 2,
        "+": 2,
        "-": 2,
        "min": 2,
        "max": 2,
        "delete": 2,
        "len": 1,
        "elem": 2,
        "drop": 2,
        "take": 2,
        "count": 2,
        "last": 1,
        "lastOfTwo": 2,
    }

lists = {
        "null"          : "[{0}] -> Bool",
        "++"            : "[{0}] -> [{0}] -> [{0}]",
        "rev"           : "[{0}] -> [{0}]",
        "zip"           : "[{0}] -> [{0}] -> [({0},{0})]",
        "delete"        : "Nat -> [Nat] -> [Nat]",
        "len"           : "[{0}] -> Nat",
        "elem"          : "Nat -> [Nat] -> Bool",
        "drop"          : "Nat -> [{0}] -> [{0}]",
        "take"          : "Nat -> [{0}] -> [{0}]",
        "count"         : "Nat -> [Nat] -> Nat",
        "map"           : "({0} -> {0}) -> [{0}] -> [{0}]",
        "takeWhile"     : "({0} -> Bool) -> [{0}] -> [{0}]",
        "dropWhile"     : "({0} -> Bool) -> [{0}] -> [{0}]",
        "filter"        : "({0} -> Bool) -> [{0}] -> [{0}]",
        "butlast"       : "[{0}] -> [{0}]",
        "last"          : "[Nat] -> Nat",
        "sorted"        : "[Nat] -> Bool",
        "insort"        : "Nat -> [Nat] -> [Nat]",
        "ins"           : "Nat -> [Nat] -> [Nat]",
        "ins1"          : "Nat -> [Nat] -> [Nat]",
        "sort"          : "[Nat] -> [Nat]",
        "butlastConcat" : "[{0}] -> [{0}] -> [{0}]",
        "lastOfTwo"     : "[Nat] -> [Nat] -> Nat",
        "zipConcat"     : "{0} -> [{0}] -> [{0}] -> [({0}, {0})]",
    }

trees = {
        "height" : "Tree {0} -> Nat",
        "mirror" : "Tree {0} -> Tree {0}",
    }

import re
par = re.compile("\(.*\)")
arr = re.compile("(->)")

functions  = nats.keys() + lists.keys() + trees.keys()

def fun_exists(f):
    return f in nats or f in lists or f in trees

def arity(f):
    if f in nats:
        return nats[f]
    else:
        sig = lists.get(f,trees.get(f,""))
        sig = par.sub("",sig)
        return len(arr.findall(sig))

boolfuns = ["filter", "takeWhile", "dropWhile"]

hofs = ["map"]

def depcalc(fun):
    if fun is None:
        return []
    else:
        return [fun] + depcalc(deps.get(fun, None))

th_header = "{-# LANGUAGE TemplateHaskell #-}\n"

header = """module Main where

import Prelude(undefined,Bool(..),IO,flip,($))

import HipSpec.Prelude
import HipSpec
import Definitions
import Properties

main :: IO ()
main = hipSpec {0}
"""

def unique(l):
    return list(set(l))

def generate(props, init_funs, filename=None):
    funs = unique(tuple(sum(map(depcalc, init_funs), [])))
    # print init_funs, funs

    use_nats = any(f in nats for f in funs)
    use_hof = any(f in hofs for f in funs)
    use_boolfun = any(f in boolfuns for f in funs)
    use_list = any(f in lists for f in funs)
    use_trees = any(f in trees for f in funs)

    ty = 'Nat' if use_nats else 'A'

    if filename is None:
        res = th_header
        filename = "$(fileName)"
    else:
        res = ""
        filename = '"{0}"'.format(filename)

    res += header.format(filename)

    res += """    [ vars ["x", "y", "z"] (undefined :: {0})\n""".format(ty)

    if use_list:
        res += """    , vars ["xs", "ys", "zs"] (undefined :: [{0}])\n""".format(ty)

    if use_trees:
        res += """    , vars ["r", "s", "t"] (undefined :: Tree {0})\n""".format(ty)

    if use_hof:
        res += """    , vars ["f", "g"] (undefined :: {0} -> {0})\n""".format(ty)

    if use_boolfun:
        res += """    , vars ["p", "q"] (undefined :: {0} -> Bool)\n""".format(ty)

    res += "    -- Constructors\n"

    if use_nats:
        res += """    , "Z" `fun0` Z\n"""
        res += """    , "S" `fun1` S\n"""

    if use_list:
        res += """    , "[]" `fun0` ([] :: [{0}])\n""".format(ty)
        res += """    , ":"  `fun2` ((:) :: {0} -> [{0}] -> [{0}])\n""".format(ty)

    if use_trees:
        res += """    , "Leaf" `fun0` (Leaf :: Tree {0})\n""".format(ty)
        res += """    , "Node" `fun3` (Node :: Tree {0} -> {0} -> Tree {0} -> Tree {0})\n""".format(ty)

    res += "    -- Functions\n"

    for f in funs:
        if fun_exists(f):
            sig = lists.get(f,trees.get(f,"")).format(ty)
            # print f, sig, bool(sig)
            if sig:
                res += """    , "{0}" `fun{1}` (({0}) :: {2})\n""".format(f, arity(f), sig)
            else:
                res += """    , "{0}" `fun{1}` ({0})\n""".format(f, arity(f))

    if use_boolfun or use_hof:
        res += "    -- Observers\n"
        if use_boolfun:
            res += """    , observer2 (flip ($) :: {0} -> ({0} -> Bool) -> Bool)\n""".format(ty)
        if use_hof:
            res += """    , observer2 (flip ($) :: {0} -> ({0} -> {0}) -> {0})\n""".format(ty)

    res += "    ]\n\n"

    to_show = ",".join("prop_" + p for p in props)

    res += "to_show = ({0})".format(to_show)

    return res

def main():
    import sys
    if sys.argv[1] == 'all' or sys.argv[1] == 'all_th':
        th = sys.argv[1] == 'all_th'

        content = open('Properties.hs', 'r')

        row = "start"

        gen = {}

        while row:
            row = content.readline()
            if row[0:5] == "prop_" and "::" not in row:
                prop = row[5:7]
            else:
                continue
            funs = []
            while row != "\n" and row:
                row = content.readline()
                for f in functions:
                    fs = map(lambda s:s.format(f),
                             ('({0} ',' {0})',
                              '[{0} ',' {0}]',
                              ' {0} ',
                              '`{0}`'))
                    if f not in funs and any(ff in row for ff in fs):
                        funs.extend([f])

            funs = tuple(funs)

            gen[funs] = gen.get(funs, []) + [prop]

        for funs in gen:
            props = gen[funs]
            hs_file_name = 'Part{0}.hs'.format("_".join(props))
            with open(hs_file_name, 'w') as hs:
                hs.write(generate(props, funs, None if th else hs_file_name))
            print hs_file_name

    else:
        props = []
        funs = []
        for x in sys.argv[1:]:
            if x.isdigit():
                props.extend([x])
            else:
                funs.extend([x])
        print generate(props, funs)

if __name__ == "__main__":
    main()


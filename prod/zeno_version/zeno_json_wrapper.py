
# Zeno says this when proved:

# Searching for proofs... 
# Proved "PropT02.prop_T02 : length ((x ++ y)) = length ((y ++ x))"

# When failed:
# Could neither prove nor disprove: 
# "PropT01.prop_T01 : double x = (x + x)"

# When timeout:
# Timed out (1s)

# Assumes only one property in the file
def zeno(file):
    import subprocess as sub
    print file
    p = sub.Popen(['zeno',file,'-t','30'],stdout=sub.PIPE,stderr=sub.PIPE)
    output, errors = p.communicate()
    if "Proved" in output:
        proved = "true" 
    else:
        proved = "false"
    print proved
    return proved

def main():
    from sys import argv
    files = argv[1:]
    d = {}
    for f in files:
        d[f] = zeno(f)
    print d

if __name__ == '__main__':
    main()


def main():

    content = open('ZenoVersion.hs', 'r')

    skeleton = open('Definitions.skeleton', 'r').read()

    row = "start"

    while row:
        row = content.readline()
        if row[0:5] == "prop_":
            prop = row[5:8]
        else:
            continue
        prows = []
        while row != "\n" and row:
            prows.extend([row])
            row = content.readline()

        module_name = 'Prop{0}'.format(prop)
        hs_file_name = '{0}.hs'.format(module_name)
        with open(hs_file_name, 'w') as hs:
            hs.write("module {0} where\n".format(module_name))
            hs.write(skeleton)
            hs.write("".join(prows))
        print hs_file_name

if __name__ == "__main__":
    main()


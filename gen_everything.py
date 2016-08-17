from os import popen

open('Everything.agda', 'w').write(
    '\n'.join(
        ['module Everything where\n'] +
        ['import ' + line[:-6].replace('/', '.') for line in popen('find Cat -name \\*.agda')]))

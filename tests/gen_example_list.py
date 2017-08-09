import os

cwd = os.getcwd()
ex = cwd[:cwd.rfind('/')] + '/examples'

with open('example_list.m', 'w') as f:
  for e in os.listdir(ex):
    f.write('load "' + ex + '/' + e + '";\n')


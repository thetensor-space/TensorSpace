import os

def parse_spec(lines):
  new_lines = []
  for i in range(len(lines)):
    l = lines[i].replace(' ', '').replace('\t', '').replace('\n', '')
    if l != '':
      new_lines += [l]
  lines = new_lines
  files = []
  name = ''
  i = 0
  while i < len(lines):
    if lines[i] == '{':
      name += '/'
    elif lines[i] == '}':
      name = name[:-1]
      try:
        j = name.rindex('/')
        name = name[:j+1]
      except ValueError:
        name = ''
    else:
      if lines[i+1] == '{':
        name += lines[i]
      else:
        files += [name + lines[i]]
    i += 1
  print("Searching Magma files...")
  for f in files:
    print("  " + f[1:])
  return files

def format_list(l):
  s = ''
  if len(l) == 0:
    return s
  for i in range(len(l)-1):
    s += l[i] + ', '
  s += l[-1]
  return s

def get_magma_intrinsics(direc, files):
  intrinsics = []
  for file in files:
    with open(direc + file) as f:
      lines = f.readlines()
    for line in [l for l in lines if l[:9] == 'intrinsic']:
      intrin = line[10:-1].replace(' ', '').replace('.', 'Any')
      i = intrin.index('(')
      name = intrin[:i]
      intrin = intrin[i+1:]
      intrin_input = []
      intrin_vars = []
      while intrin[0] != ')':
        i = intrin.find('::')
        if i != -1:
          intrin_vars += [intrin[:i].replace(',', '')]
          j = 2
          while not intrin[j] in '),':
            j += 1
          intrin_input += [intrin[i+2:j]]
          intrin = intrin[j:]
      if any(inp for inp in intrin_input if ':' in inp):
        intrin_vars[-1] += ' : parameters'
        for k in range(len(intrin_input)):
          if ':' in intrin_input[k]:
            intrin_input[k] = intrin_input[k][:intrin_input[k].index(':')]
      k = intrin.find('->')
      intrin_output = intrin[k+2:].replace(' ', '').split(',')
      intrinsics += [name + '(' + format_list(intrin_vars) + ') : ' + format_list(intrin_input) + ' -> ' + format_list(intrin_output)]
  return sorted(intrinsics)

def get_doc(direc):
  files = []
  for file in [f for f in os.listdir(direc + '/doc') if f.endswith('.tex')]:
    files += ['/doc/' + file]
  print("Searching documentation files...")
  for f in files:
    print("  " + f[1:])
  return files

def get_doc_intrinsics(direc, files):
  intrinsics = []
  for file in files:
    with open(direc + file) as f:
      lines = f.readlines()
    i = 0
    intrin_env = False
    while i < len(lines):
      if intrin_env:
        if '\end{intrinsics}' in lines[i]:
          intrin_env = False
        elif '(' in lines[i]:
          intrinsics += [lines[i][:-1]]
      else:
        if '\\begin{intrinsics}' in lines[i]:
          intrin_env = True
      i += 1
  return sorted(intrinsics)

# ------------------------------------------------------------------------------
#
# ------------------------------------------------------------------------------

no_working_spec = True
while no_working_spec:
  pack_dir = input("Package directory: ")
  if len(pack_dir) > 0:
    if pack_dir[-1] == "/":
      pack_dir = pack_dir[:-1]
    try: 
      i = pack_dir.rindex("/")
      pack_name = pack_dir[i+1:]
    except ValueError:
      pack_name = pack_dir
    spec_file = pack_dir + "/" + pack_name + ".spec"

    try:
      with open(spec_file) as f:
        lines = f.readlines()
      no_working_spec = False
    except FileNotFoundError:
      print("\nFollowing spec file not found!\n  " + spec_file)

print("\n--------------------------------------------")
print("Package name: " + pack_name)
print("   Directory: " + pack_dir)
print("   Spec file: " + pack_name + ".spec")
print("--------------------------------------------")
magma_files = parse_spec(lines)
magma_intrin = get_magma_intrinsics(pack_dir, magma_files)
if len(magma_intrin) > 0:
  print("\nFound " + str(len(magma_intrin)) + " intrinsics in Magma files.")
else:
  print("Found no intrinsics!")
print("--------------------------------------------")
doc_files = get_doc(pack_dir)
doc_intrin = get_doc_intrinsics(pack_dir, doc_files)
if len(doc_intrin) > 0:
  print("\nFound " + str(len(doc_intrin)) + " intrinsics in documentation files.")
else:
  print("Found no intrinsics!")
print("--------------------------------------------")
magma_discrep = []
doc_discrep = []
for i in magma_intrin:
  if not i in doc_intrin:
    magma_discrep += [i]
for i in doc_intrin:
  if not i in magma_intrin:
    doc_discrep += [i]
print("Found " + str(len(magma_discrep)) + " discrepencies with the Magma files.")
print("Found " + str(len(doc_discrep)) + " discrepencies with the documentation files.")
with open(pack_dir + "/tests/IntrinsicOutput.txt", 'w') as result:
  result.write("Magma file discrepencies:\n")
  for i in range(len(magma_discrep)):
    result.write("  " + magma_discrep[i] + "\n")
  result.write("\n" + "-"*80 + "\n\n")
  result.write("-"*80 + "\n\n")
  result.write("Documentation file discrepencies:\n")
  for i in range(len(doc_discrep)):
    result.write("  " + doc_discrep[i] + "\n")
print("Results printed out to " + pack_dir + "/tests/IntrinsicOutput.txt")

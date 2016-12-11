import glob, os
dir_name = input('Directory:')

os.chdir(dir_name)
for file_name in glob.glob("*.tex") :
  doc = open( file_name, 'r' )

  if not os.path.exists('MAGMATranslation/'):
    os.makedirs('MAGMATranslation/')

  out = open( 'MAGMATranslation/' + file_name, 'w' )

  lines = doc.readlines()
  doc.close()

  endintro = False
  des = False
  para = False
  Type = False

  out_lines = []

  for l in lines :
    if des :
      l = '\n\des' + l
      des = False
      para = False
    if para :
      l = '\n\\var\n' + l
    if 'subsubsection{' in l :
      newline = '\\subsubsection' 
      newline += l.replace('\\subsubsection','').replace(' ','-')
      newline += l.replace('\\subsubsection{','').replace('}','')
      newline += '\n\\intro' + '\n'
      endintro = True
    elif 'subsection{' in l :
      newline = '\\subsection' 
      newline += l.replace('\\subsection','').replace(' ','-')
      newline += l.replace('\\subsection{','').replace('}','')
      newline += '\n\\intro' + '\n'
      endintro = True
    elif 'section{' in l :
      newline = '\\section' 
      newline += l.replace('\\section','').replace(' ','-')
      newline += l.replace('\\section{','').replace('}','')
      newline += '\n\\intro' + '\n'
      endintro = True
    elif 'color{' in l and 'blue' in l : 
      if endintro :
        newline = '\\endintro\n\n'
      else :
        newline = ''
      endintro = False
    elif 'index{' in l :
      newline = ''
    elif 'small' in l and 'verbatim' in l :
      if '%%Type' in l :
        newline = ''
        Type = True
      else : 
        newline = '\\sig\n'
    elif 'end' in l and 'verbatim' in l :
      newline = ''
    elif 'begin' in l and 'lstlisting' in l :
      newline = '\\begincode\n'
    elif 'color{' in l and 'black' in l :
      newline = ''
      if not Type :
        des = True
      else : 
        Type = False
    elif '%%Example' in l :
      newline = '\\beginex{'
      i = l.index('{') + 1
      j = l.index('}')
      newline += l[i:j] + '}\n'
    elif 'end' in l and 'lstlisting' in l :
      newline = '\\endcode\n'
    elif 'usepackage' in l : 
      newline = ''
    elif 'DeclareMath' in l :
      newline = ''
    elif 'newtheorem' in l :
      newline = ''
    elif 'newcommand' in l :
      newline = ''
    elif 'begin' in l and 'document' in l :
      newline = ''
    elif 'end' in l and 'document' in l : 
      newline = ''
    elif 'maketitle' in l :
      newline = ''
    elif 'tableofcontents' in l :
      newline = ''
    elif 'makeindex' in l :
      newline = ''
    elif 'documentclass' in l :
      newline = ''
    elif '{\\small' in l :
      newline = ''
    elif l.replace(' ','') == '}\n' or l.replace(' ','') == '{\n' :
      newline = ''
    else :
      newline = l
    if 'parameters)' in newline :
      para = True
      newline = newline.replace( ':', '$\colon$', 1 )
    out_lines.append(newline)


  for l in out_lines :
    out.write(l)

  out.close()




  


\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{documentation}[2017/05/17 Documentation Class]

% Based on the amsbook class
\LoadClass[11pt]{amsbook}

% Packages required
\RequirePackage{hyperref}
\RequirePackage[shortalphabetic]{amsrefs}
\RequirePackage[margin=1in]{geometry}
\RequirePackage{amsmath}
\RequirePackage{amsthm}
\RequirePackage{amssymb}
\RequirePackage{xcolor}
\RequirePackage{listings}
\RequirePackage{framed}
\RequirePackage{anyfontsize}

% Version number of the package
\newcommand{\version}[1]{\def \@versionnumber{#1}}
\renewcommand{\copyrightyear}[1]{\def \@copyrightyear{#1}}

% Modified from amsbooks to edit title page
\renewcommand{\author}[2][]{%
  \ifx\@empty\authors
    \gdef\authors{#2}%
    \gdef\addresses{\author{#2}}%
  \else
    \g@addto@macro\authors{, #2}%
    \g@addto@macro\addresses{\author{#2}}%
  \fi
  \@ifnotempty{#1}{%
    \ifx\@empty\shortauthors
      \gdef\shortauthors{#1}%
    \else
      \g@addto@macro\shortauthors{\and#1}%
    \fi
  }%
}
\edef\author{\@nx\@dblarg
  \@xp\@nx\csname\string\author\endcsname}
\def\@setaddresses{\par
  \nobreak \begingroup
  \def\author##1{\begingroup
    \nobreak\addvspace\bigskipamount 
    {\fontsize{18}{12}\selectfont \bfseries ##1}
    \endgroup}%
  \def\address##1##2{\begingroup
    \par\addvspace\bigskipamount\indent
    \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\fontsize{12}{12}\selectfont\ignorespaces##2}\par\endgroup}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak\indent
      \@ifnotempty{##1}{, \ignorespaces##1\unskip}
      \ttfamily##2\par}\vspace{50pt}\endgroup}%
  \addresses
  \endgroup}
\def\maketitle{\par
  \@topnum\z@ % this prevents figures from falling at the top of page 1
  \begingroup
  \@maketitle
  \endgroup
  \c@footnote\z@
  \def\do##1{\let##1\relax}%
  \do\maketitle \do\@maketitle \do\title \do\@xtitle \do\@title
  \do\author \do\@xauthor \do\address \do\@xaddress
  \do\email \do\@xemail \do\curraddr \do\@xcurraddr
  \do\dedicatory \do\@dedicatory \do\thanks \do\thankses
  \do\keywords \do\@keywords \do\subjclass \do\@subjclass
}
\def\@maketitle{%
  \cleardoublepage \thispagestyle{empty}%
  \begingroup \topskip\z@skip
  \null\vfil
  \begingroup 
  \vspace{50pt}
  \fontsize{36}{12}\selectfont \bfseries \centering
  \openup\medskipamount
  \@title\par\vspace{150pt}
  \endgroup
  \vfil
  \begingroup
    \centering
    {\fontsize{10}{12}\selectfont\@setaddresses}
  \endgroup
  \vfill
  \ifx\@empty\@versionnumber 
  \else \begingroup
    \centering 
    {\fontsize{12}{14}\selectfont Version \@versionnumber \\ \@date}\par
    \endgroup
  \fi
  \newpage\thispagestyle{empty} % copyright page
  \topskip\z@skip
  \null\vfil
  \begingroup
    \centering 
    \copyright \@copyrightyear\; \authors \par
  \endgroup
  \endgroup}


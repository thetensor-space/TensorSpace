\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{documentation}[2017/05/17 Documentation Class]

% Based on the amsbook class
\LoadClass[11pt]{amsbook}

% Packages required
\RequirePackage{hyperref}
\hypersetup{
    colorlinks=true,
    linkcolor=blue,
    filecolor=blue,      
    urlcolor=blue,
    citecolor=blue,
}
\RequirePackage[shortalphabetic]{amsrefs}
\RequirePackage[margin=0.75in]{geometry}
\RequirePackage{amsmath}
\RequirePackage{amsthm}
\RequirePackage{amssymb}
\RequirePackage{xcolor}
\RequirePackage{listings}
\RequirePackage{framed}
\RequirePackage{anyfontsize}
\RequirePackage{verbatim}

\makeindex
\numberwithin{section}{chapter}
\numberwithin{subsection}{section}
%\numberwithin{subsubsection}{subsection}

% Show subsections in TOC
\setcounter{tocdepth}{2}
\def\l@subsection{\@tocline{2}{0pt}{2pc}{5pc}{}} % redefined so subsections indent further

% Version number of the package
\newcommand{\version}[1]{\def \@versionnumber{#1}}
\renewcommand{\copyrightyear}[1]{\def \@copyrightyear{#1}}

% Defines `intrinsics' environment---similar to verbatim
\newenvironment{intrinsics}%
  {
    \endgraf\color{black!20!blue}\small
    \endgraf\verbatim
  }
  {
    \endverbatim
  }

% Defines `example' environment
\newcounter{examplecounter}
\newenvironment{example}[1][]
  {
    \refstepcounter{examplecounter}
    \begin{framed}
      \noindent \textbf{Example \theexamplecounter.}\; \texttt{\large #1}\par
      \small
  }
  {
    \end{framed}
    \bigskip
  }
\numberwithin{examplecounter}{chapter}

% Defines `code' environment, which is used to display code
\lstnewenvironment{code}
  {
    \lstset{frame=single,basicstyle=\ttfamily\color{black},
    backgroundcolor=\color{white!85!gray}}
  }
  {}

% NOTICE: the code that follows comes from amsbook.cls
%
% Latest versions of the amsbook class can be found at the AMS website:
% http://www.ams.org/publications/authors/tex/amslatex
% 
% A direct link to download the AMS classes:
% http://mirrors.ctan.org/macros/latex/required/amscls.zip


% Modified from amsbook.cls to edit title page, second page, and index
% Along with comments documenting all changes made
% The original class file (amsbook.cls) can be found at the above websites
\renewcommand{\author}[2][]{%
  \ifx\@empty\authors
    \gdef\authors{#2}%
    \gdef\addresses{\author{#2}}% Added to include authors in addresses
  \else
    \g@addto@macro\authors{, #2}% Replaced \and with ', '
    \g@addto@macro\addresses{\author{#2}}% Included authors in addresses
  \fi
  \@ifnotempty{#1}{%
    \ifx\@empty\shortauthors
      \gdef\shortauthors{#1}%
    \else
      \g@addto@macro\shortauthors{\and#1}%
    \fi
  }%
}

\def\@setaddresses{\par
  \nobreak \begingroup
  \def\author##1{\begingroup
    \nobreak\addvspace\bigskipamount 
    {\fontsize{18}{12}\selectfont \bfseries ##1} % Included author info
    \endgroup}%
%  \def\\{\unskip, \ignorespaces}%
%  \interlinepenalty\@M
  \def\address##1##2{\begingroup
    \par\addvspace\bigskipamount\indent
    \@ifnotempty{##1}{(\ignorespaces##1\unskip) }%
    {\fontsize{12}{12}\selectfont\ignorespaces##2}\par\endgroup}% Changed font size and removed small caps
%  \def\curraddr##1##2{\begingroup
%    \@ifnotempty{##2}{\nobreak\indent\curraddrname
%      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
%      ##2\par}\endgroup}%
  \def\email##1##2{\begingroup
    \@ifnotempty{##2}{\nobreak%\indent %\emailaddrname
      \@ifnotempty{##1}{, \ignorespaces##1\unskip} %\/:\space
      \ttfamily##2\par}\vspace{50pt}\endgroup}% Added spacing
%  \def\urladdr##1##2{\begingroup
%    \def~{\char`\~}%
%    \@ifnotempty{##2}{\nobreak\indent\urladdrname
%      \@ifnotempty{##1}{, \ignorespaces##1\unskip}\/:\space
%      \ttfamily##2\par}\endgroup}%
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
  \vspace{50pt} % Added spacing
  \fontsize{36}{12}\selectfont \bfseries \centering % Changed font size
  \openup\medskipamount
  \@title\par\vspace{150pt} % Added spacing
%  \def\and{\par\medskip}\centering
%  \mdseries\authors\par\bigskip
  \endgroup
  \vfil
%  \ifx\@empty\addresses \else \@setaddresses \fi
%  \vfil
%  \ifx\@empty\@dedicatory
%  \else \begingroup
%    \centering{\footnotesize\itshape\@dedicatory\@@par}%
%    \endgroup
%  \fi
%  \vfill
%
% Replaced above 8 lines of tex with the following 11 lines of tex
% This changes the formatting of the address and includes different information
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
  \newpage\thispagestyle{empty} % Now this is the copyright page
%  \begin{center}
%    \ifx\@empty\@subjclass\else\@setsubjclass\fi
%    \ifx\@empty\@keywords\else\@setkeywords\fi
%    \ifx\@empty\@translators\else\vfil\@settranslators\fi
%    \ifx\@empty\thankses\else\vfil\@setthanks\fi
%  \end{center}
%  \vfil
%  \@setabstract
%
% Replaced the above 8 lines of tex with the following 7 lines
% This formats the second page to be a copyright page
  \topskip\z@skip
  \null\vfil
  \begingroup
    \centering 
    Copyright \@copyrightyear\; \authors \par
  \endgroup
  \endgroup}

% Index
\def\indexname{Intrinsics} % Changed the name 
\def\@idxitem{\tt\par\hangindent 2em} % Changed font to tt


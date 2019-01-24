
<a href="https://www.codecogs.com/eqnedit.php?latex=\langle~t~|" target="_blank"><img src="https://latex.codecogs.com/gif.latex?\langle~t~|" title="\langle~t~|" /></a>

The Experimental Multilinear Algebra Group's distribution of software for 
integration in the computer algebra system MAGMA, V2.22 and beyond.

This software was created by Joshua Maglione and James B. Wilson, Copyright 
2016--2019. Distributed under MIT License.

If you want a copy of the software under a different license, please contact the
authors. 


## Package Contents 

  1. Spec file is `./TensorSpace.spec`
  2. Source Code is contained in the folder `src`
  3. Examples are included in the folder `examples`
  4. Documentation is included as `TensorSpace.pdf` in `doc`
  5. Example files are demonstrated in `TensorSpace.pdf` and their file names 
     coincide with their example title in the text.
  6. Performance and debugging tests are contained in the folder `tests`


## Installation

#### Linux and Mac users

To install the package, run the following shell command:
```
$ sh install.sh
```
This will 
  1. download dependencies and
  2. edit your Magma start file to load this on start up.


#### Manually

Currently, we do not have an install file compatible with Windows. Instead, 
attach the spec file during a Magma run and the intrinsics will be available
to use.  To attach the spec file run the following, where `<location>` is the 
directory containing the TensorSpace directory,
```
> AttachSpec("<location>/TensorSpace/TensorSpace.spec");
```


## Updates

##### Linux and Mac users

To update the package and all its dependencies, run the following shell command:
```
$ sh update.sh
```

#### Manually

Latest versions can be downloaded on GitHub at: 
<https://github.com/algeboy/TensorSpace>


## Feedback, Bugs, and Contributions

We welcome general feedback about the package and challenging examples. To 
report bugs, please create an "Issue" on eMAGma repository site on GitHub. 
Contributions are always welcome. To contribute, please fork a copy of 
TensorSpace and create a pull request.



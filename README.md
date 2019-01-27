Tensors mean different things to different people.
![Tensors across the sciences](tensor-mix.png)

So we decided why not abstract the differences into _Tensor Spaces_. Now all it means to be a tensor is...
> A tensor is an element of a tensor space.


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

Download Latest Release zip file and unzip into a folder into 
magma you would like your Magma packages installed, e.g.:
```
$ mkdir my_magma_packages
$ cd my_magma_packages
$ gzip TensorSpace-2.2.zip
```
Then install the package by running the following shell command:
```
$ sh install.sh
```
This will may install further packages necessary in the same directory.  
It will also modify your Magma start up file so that these packages 
are available at start up of Magma.  To avoid this, use manual installation
instructions below.


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

## Uninstalling

This package can be removed entirely by deleting the folder into which it was downloaded and removing the 
following lines from you `/.magmarc` file.
```
AttachSpec("<location>/TensorSpace/TensorSpace.spec");
```


## Feedback, Bugs, and Contributions

We welcome general feedback about the package and challenging examples. To 
report bugs, please create an "Issue" on TensorSpace repository site on GitHub. 
Contributions are always welcome. To contribute, please fork a copy of 
TensorSpace and create a pull request.



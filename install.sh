# Vars
FILE="$(realpath -s "$0")"              # Full path to this file
DIR="$(dirname $FILE)"                  # Current directory
PKGDIR="$(dirname $DIR)"                # Directory for dependencies
START="${HOME}/.magmarc"                # Magma start file location

# Dependencies and .spec locations
ATTACH="AttachSpec(\"$DIR/TensorSpace.spec\");"


echo "TensorSpace.spec is in $DIR"


# Construct Magma start file

if [ -f "$START" ]
then
    echo "Found a Magma start file"
    if grep -Fxq "$ATTACH" "$START"
    then
        echo "Already installed"
    else
        echo "$ATTACH" >> "$START"
        echo "Successfully installed"
    fi
else
    echo "Creating a Magma start file: $START"
    echo "// Created by an install file for Magma start up." > "$START"
    echo "$ATTACH" >> "$START"
    echo "Successfully installed"
fi


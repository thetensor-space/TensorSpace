FILE="$(realpath -s "$0")"
DIR="$(dirname $FILE)"
START="${HOME}/.magmarc"
ATTACH="AttachSpec(\"$DIR/TensorSpace.spec\");"

if [ -f "$START" ]
then
    echo "Found a Magma start file"
    if grep -Fxq "$ATTACH" "$START"
    then
        echo "TensorSpace already installed"
    else
        echo "$ATTACH" >> "$START"
        echo "Successfully installed"
    fi
else
    echo "Creating a Magma start file: $START"
    echo "$ATTACH" > "$START"
    echo "Successfully installed"
fi


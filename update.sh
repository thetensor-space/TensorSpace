# Maybe we can make this git independent or safer?

# Location of current directory
BASEDIR=$(dirname "$0")
cd "$BASEDIR" 

# Update main git directory
echo "Updating TensorSpace package..."
git -q pull origin master 
echo "Successfully updated!"

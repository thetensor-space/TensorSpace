# Update main directory
BASEDIR=$(dirname "$0")
cd "$BASEDIR" 
# Maybe we can make this git independent or safer?
git pull origin master 

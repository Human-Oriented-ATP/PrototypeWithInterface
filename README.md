# Prototype for an extension of ROBOT with a web interface
All interesting content is found in the src directory
- src/robot contains the "Robot" (Haskell) code  - the actual mathematical content lies here
- src/APICode contains Haskell code which controls how the server works. The server right now acts as a simple API which accepts POST requests to perform moves in a web interface
- src/static contains HTML/CSS/JS controlling how the front-end webapp works. This webapp makes POST requests to the server to make moves.
 - src/static/problem contains the code for the main interface right now (this is the part of the webapp users will see when solving a problem)
 - src/static/homepage will contain what you'd expect
- src/Lib.hs is the beating heart of the server and is where the code runs for the server is actually called and runs

## To-do
- Think about library search and implement a simple system.
- Existence moves
- Think about how the interface will work with library search and start implementing.

- Write some basic template code to choose moves automatically and start playing with move scoring.

## Running the code
To run the API code, use stack (https://docs.haskellstack.org/en/stable/). First build the project with stack build (this will probably install a bunch of things), then when you want to run the web server use stack run. To access the interface, open the problem.html file in your favourite web browser (developed in Chrome, so I can't guarantee it will run smoothly in others). It will probably be empty (because I currently have the problem state saved in my browser's localStorage) - it's not difficult getting a test problem state - message me and I'll be happy to help with that. This should become irrelevant soon when we build a place to input problems on the homepage.

Let me know if you have any issues and I'll be happy to help!

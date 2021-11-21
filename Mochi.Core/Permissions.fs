namespace Mochi.Core

module Permissions = 
    
    let map = Map.ofList [
        ("FileRead", 0)
        ("FileWrite", 1)
        ("FileDelete", 2)
    ]
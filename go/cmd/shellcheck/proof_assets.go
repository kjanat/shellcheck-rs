package main

// Reviewed archive subjects and hashes of their verified native members.
var reviewedAssets = map[string]assetProof{
	"aarch64-apple-darwin":           {archiveSHA256: "184fc672a93d48153383f41c4aaf3bc28a73dcbcee4dc89143626176c416da8b", binarySHA256: "a4c1fd13f93153aa54d77b7ff0f5e6ccde9afa045e2864b95e66d914f4f8e4b5"},
	"aarch64-linux-android":          {archiveSHA256: "01eebdda53913c35fc676dacfa80550ad231a71008882c04771b25e156457ae2", binarySHA256: "49ea52f017ebe7d9a724d555e0fd72fb5ca5c48d0aebbcd7a88d53fa51b029d3"},
	"aarch64-pc-windows-msvc":        {archiveSHA256: "08b527a6dbf8b6e3872a83275dbfbb166761b029b1f91c84e686c358c4832ca0", binarySHA256: "8ca29c2efc7fd5c15dde4faad4490f26a60a763051c68f0b1856cc19eb74912f"},
	"aarch64-unknown-linux-musl":     {archiveSHA256: "598f5f580afac4c4fb1197ce9d531060b0ab195d4adbc75d2ffeecdedf426d3f", binarySHA256: "31990d0687146e01ddbd193e45ee3f91003627b7750a08fa7e4f2bab96b1e24d"},
	"armv7-linux-androideabi":        {archiveSHA256: "3fa307360300085584655443809c722f04da1613b119cc7a787c5a38c42ebc24", binarySHA256: "6e9d97749fe6a7ed2a0ddf3f82da8cd9f00ef81683e20d316ce431c95460e1c7"},
	"armv7-unknown-linux-musleabihf": {archiveSHA256: "9e0645a75acc24a57554c997ea03a8ec01b6334298f4522266867685f3571017", binarySHA256: "b80b2c9dcd74cbcf1396f55835df9547a90dd78aff6ff2edf41174920e1a5268"},
	"i686-linux-android":             {archiveSHA256: "eed90421c46c371e0a09c5b6eaa1e5d800d928cb59de5ab0e3c2532850f98b6b", binarySHA256: "060d8ce3280d2ec62751b344859e839168b1d0467aa1ba1593bcddf213cb30e2"},
	"i686-pc-windows-msvc":           {archiveSHA256: "e94d14bcc1a29e11a367a5b756bec00f7b8954432854643f79eb644d5db0f9ec", binarySHA256: "45b555ad6d48c9102948003985a035e763f0a024fa9baeae474473f4de1613ed"},
	"i686-unknown-freebsd":           {archiveSHA256: "f94f813fa428eebb7c70eac7c8d9e9b0b07aa0160302683193ae02d953abe990", binarySHA256: "bcc701ec49fd7ef41c24e7326be172038b012bb6a7c447d55207679cbe22a01e"},
	"i686-unknown-linux-musl":        {archiveSHA256: "a2cf978c53c5ed5cc30393987c3b2405d2725623a4c25ddbd6d654a623d6cb56", binarySHA256: "846be8bcab1943c8764fa73ba6b55af9374a4d5d5e2b14dcf612459045598442"},
	"x86_64-apple-darwin":            {archiveSHA256: "f336d06a94f0c629d4b29b19d78081a1be2aab00c9a61f3b788fe28333c5ffd4", binarySHA256: "d17410a71281dca0359fed9ae9d894ee05ca8c4633d902e39220fd7ff9dece70"},
	"x86_64-linux-android":           {archiveSHA256: "b3c1cb2571690d342c6cae0d28c99726cad0a8a4abf286cc067deceada6a9753", binarySHA256: "1ea042343d24790e340893392ffbaa37669dea7f916d4ca211eff517d8f7d2c7"},
	"x86_64-pc-windows-msvc":         {archiveSHA256: "c4ad4f6d17150d4acaa03d0666c5fc4ad88ce2a1918b4a21b2e103fc34d2ea43", binarySHA256: "145fb8015d27c39426e40003a132f23eeaee172caaf6418bbe3cc05d43377147"},
	"x86_64-unknown-freebsd":         {archiveSHA256: "020fca849b21a186c97271029447fd000c7cecf6c775b0b7eb49c4746e3bdbd6", binarySHA256: "57c58d70f0f925698d0374bce54835e9bb4c260980d751e7191a3e516a579c24"},
	"x86_64-unknown-linux-musl":      {archiveSHA256: "32352bd1df8047f70a8e41359c252ae2f7e5e640007ba8f11eefcaa755b110a5", binarySHA256: "2369eddb54942a63d8cec4ebd5ed23c8b65cf7dd59c4664e19d7263235c96345"},
}

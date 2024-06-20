const Http = require('http')
const {arrayToUtf8} = require('../src/sm2/utils')
const sm2 = require('../src/index').sm2

const cipherMode = 1 // 1 - C1C3C2，0 - C1C2C3
const msgString = '测试国密SM2'

const myPublicKey = '0416aebc0d9a00f5d82b9aa764425437caf9046ef149475c4add632c9372ef7fbf338e1049f00c71b5e59918e46da09b2a3c6a4deea64316187267d5b533ee2ea9'
const myPrivateKey = '00c41eb1e2f917d8e6e2845b456fd8a15568f1d4a3016b297cfc786e164225e29c'
const myuserid = '78CFCC02D41F489FA3A0D04A81C67450' // 已经转成16进制 userid
const yourPublicKey = '045bd655aa66b20bbb9875c6196c6c552e39a1d17690672f0789064097dd12b5c67f12b62ae75a85abb51eba669bc685165e4230b204a1fb12e9b0a145f04b0b3d'

// 构建原始报文
const reqData = {
  xmsfzmd518: '0d7bfc5a0a32e1ab66bad5832cd8a2b8',
  xm: '鬼剑士',
  sfz: '110229194902154016',
}
const reqJson = JSON.stringify(reqData)
const reqDataEncrypt = sm2.Encrypt(reqJson, yourPublicKey, 1)
const reqSign = sm2.Sign(reqDataEncrypt, myPrivateKey, {
  userId: myuserid,
  der: true, // asn.1 der 编码
  hash: true, // sm3杂凑
  userIdType: 'Hex', // 指定userid的值已经是16进制数据 如果userid 为  xuzhqiang0001 则不需要指定useridType。
  dataType: 'Hex', // 指定加密的字符串的值已经是16进制 如果是明文则不需要指定dataType。
})
const postdata = {
  data: reqDataEncrypt,
  sign: reqSign,
  code: myuserid
}
const data = JSON.stringify(postdata)
let responseData = {}
// 请求java hutool的sm2加密解密
const req = Http.request({
  host: 'localhost',
  port: 30030,
  path: '/auth/qrcode',
  method: 'POST',
  headers: {
    'Content-Type': 'application/json',
    'Content-Length': data.length
  },
}, (res) => {
  let resData = ''
  res.on('data', response => {
    resData += response.toString('utf8')
  })
  res.on('end', () => {
    responseData = JSON.parse(resData)
    // 验证返回的签名
    const verifySign = sm2.VerifySign(responseData.data.data, responseData.data.sign, yourPublicKey, {
      userId: myuserid,
      der: true, // asn.1 der 编码
      hash: true, // sm3杂凑
      dataType: 'Hex',
      userIdType: 'Hex' // 指定userid的值已经是16进制数据 如果userid 为  xuzhqiang0001 则不需要指定useridType。
    })
    console.log(verifySign)
  })
})
req.write(data)
req.end()
